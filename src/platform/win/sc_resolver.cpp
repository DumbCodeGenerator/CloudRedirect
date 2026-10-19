#include "sc_resolver.h"
#include "sig_scanner.h"
#include "log.h"

#define WIN32_LEAN_AND_MEAN
#include <windows.h>
#include <cstring>

namespace ScResolver {

// ── Helpers ───────────────────────────────────────────────────────────

// Find the Nth call target (E8 rel32) scanning from `start` within `maxBytes`.
static uintptr_t FindNthCallTarget(uintptr_t start, size_t maxBytes, int n) {
    if (!start || !maxBytes || n < 1) return 0;
    int count = 0;
    __try {
        const auto* p = reinterpret_cast<const uint8_t*>(start);
        for (size_t i = 0; i + 5 <= maxBytes; ++i) {
            if (p[i] == 0xE8) {
                int32_t disp = *reinterpret_cast<const int32_t*>(p + i + 1);
                uintptr_t target = start + i + 5 + disp;
                if (target >= SigScanner::GetImageBase() &&
                    target < SigScanner::GetImageBase() + SigScanner::GetImageSize()) {
                    if (++count == n) return target;
                }
            }
        }
    } __except (EXCEPTION_EXECUTE_HANDLER) {}
    return 0;
}

// Find a string in .rdata, then locate the first LEA xref in .text that
// references it, and walk backward to the containing function's prologue.
static uintptr_t ResolveFuncByStringXref(const char* searchStr, const char* label) {
    size_t searchLen = strlen(searchStr);
    if (searchLen == 0 || searchLen >= 128) return 0;

    // Build mask (all exact)
    char mask[128];
    memset(mask, 'x', searchLen);
    mask[searchLen] = '\0';

    uintptr_t strAddr = SigScanner::FindPatternInRange(
        SigScanner::GetRdataBase(), SigScanner::GetRdataSize(),
        (const uint8_t*)searchStr, mask, searchLen);
    if (!strAddr) {
        LOG("[Resolver] %s: string '%s' not found in .rdata", label, searchStr);
        return 0;
    }

    // Find the first LEA [rip+disp] in .text that targets this string address.
    const auto* text = reinterpret_cast<const uint8_t*>(SigScanner::GetTextBase());
    size_t textSize = SigScanner::GetTextSize();

    __try {
        for (size_t i = 0; i + 7 <= textSize; ++i) {
            // Check for LEA with REX.W: 48 8D xx or 4C 8D xx where ModRM & 0xC7 == 0x05
            if ((text[i] == 0x48 || text[i] == 0x4C) && text[i+1] == 0x8D &&
                (text[i+2] & 0xC7) == 0x05) {
                uintptr_t instrAddr = SigScanner::GetTextBase() + i;
                int32_t disp = *reinterpret_cast<const int32_t*>(text + i + 3);
                uintptr_t refTarget = instrAddr + 7 + disp;
                if (refTarget == strAddr) {
                    // Walk backward to find function start (prologue + boundary check)
                    for (int back = 0; back < 0x600; back++) {
                        uintptr_t candidate = instrAddr - back;
                        if (candidate < SigScanner::GetTextBase()) break;
                        if (SigScanner::LooksLikeFunctionStart(candidate)) {
                            LOG("[Resolver] %s @ %p (RVA 0x%llX) via string xref",
                                label, (void*)candidate,
                                (uint64_t)(candidate - SigScanner::GetImageBase()));
                            return candidate;
                        }
                    }
                    break;
                }
            }
        }
    } __except (EXCEPTION_EXECUTE_HANDLER) {}

    LOG("[Resolver] %s: LEA xref walk failed", label);
    return 0;
}

// ── RTTI-based vtable resolution ──────────────────────────────────────

static uintptr_t ResolveCCMInterfaceVtable() {
    return SigScanner::ResolveVtableByRtti(".?AVCCMInterface@@");
}

static uintptr_t ResolveServiceTransportVtable() {
    return SigScanner::ResolveVtableByRtti(".?AVCClientUnifiedServiceTransport@@");
}

// ── AppInfoCache offset (dynamic) ─────────────────────────────────────
// The CSteamEngine -> CAppInfoCache offset drifts between Steam builds, so
// derive it at runtime rather than hardcoding it: every GetAppInfo call site
// loads the cache pointer with `lea reg,[engine+disp32]` just before the call.
// Collect those disp32 values into a histogram; the overwhelming majority is
// the actual offset for the running build.
static uint32_t DetectAppInfoCacheOffset(uintptr_t getAppInfoAddr) {
    if (!getAppInfoAddr) {
        LOG("[Resolver] AppInfoCache offset: GetAppInfo unresolved, cannot derive");
        return 0;
    }

    const auto* text = reinterpret_cast<const uint8_t*>(SigScanner::GetTextBase());
    size_t textSize = SigScanner::GetTextSize();
    uintptr_t textBase = SigScanner::GetTextBase();

    struct Entry { int32_t disp; int votes; };
    Entry hist[32];
    int histCount = 0;
    int totalVotes = 0;
    int callSites = 0;

    __try {
        for (size_t i = 0; i + 5 <= textSize; ++i) {
            if (text[i] != 0xE8) continue;
            int32_t rel = *reinterpret_cast<const int32_t*>(text + i + 1);
            uintptr_t target = textBase + i + 5 + rel;
            if (target != getAppInfoAddr) continue;
            ++callSites;

            // Look back over the argument setup: only count `lea reg,[reg+disp32]`
            // (mod=10) with a plain register base -- stack-frame and RIP-relative
            // encodings use different ModRM forms and are excluded naturally.
            int64_t lo = static_cast<int64_t>(i) - 96;
            if (lo < 0) lo = 0;
            for (int64_t j = static_cast<int64_t>(i) - 7; j >= lo; --j) {
                if (text[j] < 0x48 || text[j] > 0x4F) continue;
                if (text[j + 1] != 0x8D) continue;
                uint8_t modrm = text[j + 2];
                if ((modrm & 0xC0) != 0x80) continue;  // mod=10 -> disp32
                uint8_t rm = modrm & 0x07;
                if (rm == 4 || rm == 5) continue;      // SIB / RIP-relative
                int32_t disp = *reinterpret_cast<const int32_t*>(text + j + 3);
                // Only accept struct-offset magnitudes, filtering out stack slots.
                if (disp < 0x100 || disp > 0x100000) continue;
                ++totalVotes;
                int k = 0;
                for (; k < histCount; ++k) {
                    if (hist[k].disp == disp) { hist[k].votes++; break; }
                }
                if (k == histCount && histCount < 32) {
                    hist[histCount].disp = disp;
                    hist[histCount].votes = 1;
                    ++histCount;
                }
            }
        }
    } __except (EXCEPTION_EXECUTE_HANDLER) {}

    if (histCount == 0 || callSites < 5) {
        LOG("[Resolver] AppInfoCache offset: insufficient evidence (%d call site(s))", callSites);
        return 0;
    }

    int best = 0;
    for (int k = 1; k < histCount; ++k)
        if (hist[k].votes > hist[best].votes) best = k;

    // Require a minimum vote count and an overwhelming majority so a few
    // unrelated lea instructions can't skew the result.
    if (hist[best].votes < 10 || hist[best].votes * 10 < totalVotes * 7) {
        LOG("[Resolver] AppInfoCache offset: ambiguous (best 0x%X with %d/%d votes over %d call site(s))",
            hist[best].disp, hist[best].votes, totalVotes, callSites);
        return 0;
    }

    LOG("[Resolver] AppInfoCache offset detected: 0x%X (%d call site(s))",
        hist[best].disp, callSites);
    return static_cast<uint32_t>(hist[best].disp);
}

// ── Global engine pointer ─────────────────────────────────────────────
// Scan for `lea reg,[reg+<AppInfoCache offset>]` (offset derived dynamically,
// with known values as fallback) and backwalk to the preceding
// `mov reg,[rip+disp]` that loads the engine global from .data.
static uintptr_t ResolveGlobalEngine(uintptr_t scBase, uint32_t detectedOff) {
    int32_t candidates[4];
    int candidateCount = 0;
    auto addCandidate = [&](int32_t off) {
        if (off == 0) return;
        for (int k = 0; k < candidateCount; ++k)
            if (candidates[k] == off) return;
        if (candidateCount < 4) candidates[candidateCount++] = off;
    };
    addCandidate(static_cast<int32_t>(detectedOff));
    // Legacy fallbacks (newest-first) if detection was inconclusive.
    addCandidate(0x1208);   // build 11.12.30.07
    addCandidate(0x0E68);   // <= build 1782344391

    const auto* text = reinterpret_cast<const uint8_t*>(SigScanner::GetTextBase());
    size_t textSize = SigScanner::GetTextSize();
    const uintptr_t dataBase = SigScanner::GetDataBase();
    const uintptr_t dataEnd  = dataBase + SigScanner::GetDataSize();

    for (int c = 0; c < candidateCount; ++c) {
        int32_t want = candidates[c];
        __try {
            for (size_t i = 0; i + 7 <= textSize; ++i) {
                if ((text[i] == 0x48 || text[i] == 0x4C) && text[i+1] == 0x8D &&
                    (text[i+2] & 0xC0) == 0x80) {
                    int32_t disp = *reinterpret_cast<const int32_t*>(text + i + 3);
                    if (disp != want) continue;

                    uintptr_t leaAddr = SigScanner::GetTextBase() + i;

                    // Walk backward up to 40 bytes looking for `mov reg, [rip+disp]`
                    for (int back = 7; back <= 40; ++back) {
                        uintptr_t candidate = leaAddr - back;
                        if (candidate < SigScanner::GetTextBase()) break;
                        uintptr_t global = SigScanner::DecodeRipRelMov(candidate);
                        if (global && global >= dataBase && global < dataEnd) {
                            LOG("[Resolver] GlobalEngine @ %p (RVA 0x%llX) via lea+0x%X backwalk",
                                (void*)global, (uint64_t)(global - scBase), (unsigned)want);
                            return global;
                        }
                    }
                }
            }
        } __except (EXCEPTION_EXECUTE_HANDLER) {}
    }

    LOG("[Resolver] GlobalEngine: all strategies failed");
    return 0;
}

// ── CProtoBufMsg layout (dynamic) ─────────────────────────────────────
// The CProtoBufMsgBase member offsets (connection handle / EMsg / header /
// body object) drift between Steam builds, so derive them at runtime instead
// of hardcoding. The base constructor initialises the connection handle to
// 0xFFFFFFFF -- a unique anchor that pins the whole block:
//   mov dword ptr [this+CONN], 0FFFFFFFFh
// The remaining members follow at fixed deltas: EMSG=CONN+4, HDR=CONN+0xC,
// BODY=CONN+0x14 (holds for both known layouts: 0x1C/0x20/0x28/0x30 and
// 0x24/0x28/0x30/0x38). Cross-checked against the `cmp qword [this+BODY], 0`
// guard at the top of the finalize routine.
struct CpbLayout { uint32_t conn, emsg, hdr, body; };

static bool DetectCProtoBufMsgLayout(uintptr_t ctorAddr, uintptr_t finalizeAddr,
                                     CpbLayout& out) {
    uint32_t conn = 0;
    if (ctorAddr) {
        const auto* p = reinterpret_cast<const uint8_t*>(ctorAddr);
        __try {
            for (int i = 0; i < 0x80; ++i) {
                if (p[i] != 0xC7) continue;              // mov r/m32, imm32
                uint8_t modrm = p[i + 1];
                uint8_t mod = modrm >> 6, rm = modrm & 7;
                if (rm == 4 || rm == 5) continue;        // SIB / RIP-relative
                int32_t disp; int immOff;
                if (mod == 1)      { disp = (int8_t)p[i + 2];            immOff = i + 3; }
                else if (mod == 2) { disp = *reinterpret_cast<const int32_t*>(p + i + 2); immOff = i + 6; }
                else continue;                           // no displacement / register form
                uint32_t imm = *reinterpret_cast<const uint32_t*>(p + immOff);
                if (imm != 0xFFFFFFFFu) continue;
                if (disp >= 0x10 && disp <= 0x60) { conn = (uint32_t)disp; break; }
            }
        } __except (EXCEPTION_EXECUTE_HANDLER) {}
    }
    if (!conn) return false;

    uint32_t emsg = conn + 0x04;
    uint32_t hdr  = conn + 0x0C;
    uint32_t body = conn + 0x14;

    // Cross-check the finalize guard `48 83 79 <disp8> 00` (cmp qword [rcx+disp],0).
    if (finalizeAddr) {
        const auto* p = reinterpret_cast<const uint8_t*>(finalizeAddr);
        __try {
            for (int i = 0; i < 0x20; ++i) {
                if (p[i] == 0x48 && p[i + 1] == 0x83 && p[i + 2] == 0x79 &&
                    p[i + 4] == 0x00 && p[i + 3] >= 0x10 && p[i + 3] <= 0x60) {
                    if ((uint32_t)p[i + 3] != body)
                        LOG("[Resolver] CProtoBufMsg: ctor/finalize disagree (body 0x%X vs guard 0x%X), using ctor",
                            body, (uint32_t)p[i + 3]);
                    break;
                }
            }
        } __except (EXCEPTION_EXECUTE_HANDLER) {}
    }

    out.conn = conn;
    out.emsg = emsg;
    out.hdr  = hdr;
    out.body = body;
    LOG("[Resolver] CProtoBufMsg layout detected: conn=0x%X emsg=0x%X hdr=0x%X body=0x%X",
        conn, emsg, hdr, body);
    return true;
}

// ── Protobuf helpers ──────────────────────────────────────────────────
// From IDA (build 1782344391):
//
// SerializeToArray (UNIQUE at 16B, wildcarding security cookie displacement):
//   48 89 5C 24 18 55 56 57 48 81 EC 90 00 00 00 48
//   (mov [rsp+18h],rbx; push rbp; push rsi; push rdi; sub rsp,90h; mov rax,cs:cookie)
//   The `sub rsp, 90h` (0x90) is distinctive -- large stack frame for serialization.
//
// ParseFromArray is 0x410 bytes before SerializeToArray in this build. They're compiled
// together from the same TU. Once we find SerializeToArray, we scan backward for a
// function prologue within ~0x500 bytes that matches ParseFromArray's shape:
//   48 89 5C 24 10 48 89 74 24 18 55 57 41 56 48 8D 6C 24 B9 48 81 EC A0 00 00 00
//   The `sub rsp, A0h` and `lea rbp,[rsp-47h]` combo is distinctive.

static uintptr_t ResolveSerializeToArray() {
    // Prologue saves + sub rsp (wildcard) + cookie xor (48 33 C4).
    static const uint8_t pat[] = {
        0x48, 0x89, 0x5C, 0x24, 0x18,  // mov [rsp+18h], rbx
        0x55,                            // push rbp
        0x56,                            // push rsi
        0x57,                            // push rdi
        0x48, 0x81, 0xEC, 0x00, 0x00, 0x00, 0x00,  // sub rsp, ?? (wildcard)
        0x48, 0x8B, 0x05, 0x00, 0x00, 0x00, 0x00,  // mov rax, cs:cookie (wildcard)
        0x48, 0x33, 0xC4,              // xor rax, rsp
    };
    static const char mask[] = "xxxxxxxxxxx????xxx????xxx";

    uintptr_t result = SigScanner::FindPattern(pat, mask, 25);
    if (result)
        LOG("[Resolver] SerializeToArray @ %p (RVA 0x%llX) via signature",
            (void*)result, (uint64_t)(result - SigScanner::GetImageBase()));
    else
        LOG("[Resolver] SerializeToArray: signature not found");
    return result;
}

static uintptr_t ResolveParseFromArray(uintptr_t serializeAddr) {
    // Scan backward from SerializeToArray. Wildcard the lea displacement.
    static const uint8_t pat[] = {
        0x48, 0x89, 0x5C, 0x24, 0x10,  // mov [rsp+10h], rbx
        0x48, 0x89, 0x74, 0x24, 0x18,  // mov [rsp+18h], rsi
        0x55,                            // push rbp
        0x57,                            // push rdi
        0x41, 0x56,                      // push r14
        0x48, 0x8D, 0x6C, 0x24, 0x00, // lea rbp, [rsp+??] (wildcard disp)
    };
    static const char mask[] = "xxxxxxxxxxxxxxxxxx?";

    if (!serializeAddr) {
        // Try global scan if no anchor
        return SigScanner::FindPattern(pat, mask, 19);
    }

    uintptr_t scanStart = (serializeAddr > 0x1000) ? serializeAddr - 0x1000 : SigScanner::GetTextBase();
    size_t scanSize = serializeAddr - scanStart;

    uintptr_t result = SigScanner::FindPatternInRange(scanStart, scanSize, pat, mask, 19);

    if (!result) {
        // Proximity failed — try global scan as fallback
        result = SigScanner::FindPattern(pat, mask, 19);
    }

    if (result)
        LOG("[Resolver] ParseFromArray @ %p (RVA 0x%llX) via %s",
            (void*)result, (uint64_t)(result - SigScanner::GetImageBase()),
            (result >= scanStart && result < scanStart + scanSize) ? "proximity to SerializeToArray" : "global scan");
    else
        LOG("[Resolver] ParseFromArray: not found");
    return result;
}

// ── Packet routing: WrapPacket ────────────────────────────────────────
// Unique 16B signature (all position-independent):
//   48 89 5C 24 20  55  57  41 54  48 8D 6C 24 B9  48 81
// The `48 81 EC E0 00 00 00` (sub rsp, E0h) at +0x0E distinguishes it.

static uintptr_t ResolveWrapPacket() {
    // Use first 21 bytes (includes the sub rsp, E0h)
    static const uint8_t pat[] = {
        0x48, 0x89, 0x5C, 0x24, 0x20,  // mov [rsp+20h], rbx
        0x55,                            // push rbp
        0x57,                            // push rdi
        0x41, 0x54,                      // push r12
        0x48, 0x8D, 0x6C, 0x24, 0xB9,  // lea rbp, [rsp-47h]
        0x48, 0x81, 0xEC, 0xE0, 0x00, 0x00, 0x00  // sub rsp, E0h
    };
    static const char mask[] = "xxxxxxxxxxxxxxxxxxxxx";

    uintptr_t result = SigScanner::FindPattern(pat, mask, 21);
    if (result)
        LOG("[Resolver] WrapPacket @ %p (RVA 0x%llX) via signature",
            (void*)result, (uint64_t)(result - SigScanner::GetImageBase()));
    else
        LOG("[Resolver] WrapPacket: signature not found");
    return result;
}

// ── RefCountHelper ────────────────────────────────────────────────────
// Tiny function (8 bytes): mov rax,[rcx]; lock inc qword [rax]; ret
//   48 8B 01  F0 48 FF 00  C3
// This is unique in steamclient64.dll.

static uintptr_t ResolveRefCountHelper() {
    static const uint8_t pat[] = { 0x48, 0x8B, 0x01, 0xF0, 0x48, 0xFF, 0x00, 0xC3 };
    static const char mask[] = "xxxxxxxx";

    uintptr_t result = SigScanner::FindPattern(pat, mask, 8);
    if (result)
        LOG("[Resolver] RefCountHelper @ %p (RVA 0x%llX) via signature",
            (void*)result, (uint64_t)(result - SigScanner::GetImageBase()));
    else
        LOG("[Resolver] RefCountHelper: signature not found");
    return result;
}

// ── FindJob (CUtlSortedVector::Find) ─────────────────────────────────
// 24B unique: all push + sub rsp + cmp [rcx+44h],0 -- position-independent.
//   40 53 55 56 57 41 56 48 83 EC 20 83 79 44 00 4C 8B F2 48 8B F9 74 5F 8B

static uintptr_t ResolveFindJob() {
    // 22 bytes; trailing `jz short` (74) disambiguates from jz-near variant.
    static const uint8_t pat[] = {
        0x40, 0x53,              // push rbx
        0x55,                    // push rbp
        0x56,                    // push rsi
        0x57,                    // push rdi
        0x41, 0x56,              // push r14
        0x48, 0x83, 0xEC, 0x20, // sub rsp, 20h
        0x83, 0x79, 0x44, 0x00, // cmp dword ptr [rcx+44h], 0
        0x4C, 0x8B, 0xF2,       // mov r14, rdx
        0x48, 0x8B, 0xF9,       // mov rdi, rcx
        0x74,                    // jz short (distinguishes from jz near variant)
    };
    static const char mask[] = "xxxxxxxxxxxxxxxxxxxxxx";

    uintptr_t result = SigScanner::FindPattern(pat, mask, 22);
    if (result)
        LOG("[Resolver] FindJob @ %p (RVA 0x%llX) via signature",
            (void*)result, (uint64_t)(result - SigScanner::GetImageBase()));
    else
        LOG("[Resolver] FindJob: signature not found");
    return result;
}

// ── ReleaseWrapped ────────────────────────────────────────────────────
// First 21 bytes are position-independent (before the LEA with RIP-relative):
//   40 53  48 83 EC 20  8B 41 08  48 8B D9  FF C8  3D FE FF FF 00  76 28
// The `cmp eax, 0FFFFFEh` is highly distinctive.

static uintptr_t ResolveReleaseWrapped() {
    static const uint8_t pat[] = {
        0x40, 0x53,                    // push rbx
        0x48, 0x83, 0xEC, 0x20,        // sub rsp, 20h
        0x8B, 0x41, 0x08,              // mov eax, [rcx+8]
        0x48, 0x8B, 0xD9,              // mov rbx, rcx
        0xFF, 0xC8,                    // dec eax
        0x3D, 0xFE, 0xFF, 0xFF, 0x00,  // cmp eax, 0FFFFFEh
    };
    static const char mask[] = "xxxxxxxxxxxxxxxxxxx";

    uintptr_t result = SigScanner::FindPattern(pat, mask, 19);
    if (result)
        LOG("[Resolver] ReleaseWrapped @ %p (RVA 0x%llX) via signature",
            (void*)result, (uint64_t)(result - SigScanner::GetImageBase()));
    else
        LOG("[Resolver] ReleaseWrapped: signature not found");
    return result;
}

// ── BRouteMsgToJob ────────────────────────────────────────────────────
// Two approaches: signature (24B unique) AND string xref backup.
// Signature (all position-independent -- just register/stack saves):
//   4C 89 4C 24 20  4C 89 44 24 18  48 89 54 24 10  48 89 4C 24 08  55 56 57 41 54

static uintptr_t ResolveBRouteMsgToJob() {
    // Try signature first (faster)
    static const uint8_t pat[] = {
        0x4C, 0x89, 0x4C, 0x24, 0x20,  // mov [rsp+20h], r9
        0x4C, 0x89, 0x44, 0x24, 0x18,  // mov [rsp+18h], r8
        0x48, 0x89, 0x54, 0x24, 0x10,  // mov [rsp+10h], rdx
        0x48, 0x89, 0x4C, 0x24, 0x08,  // mov [rsp+8], rcx
        0x55,                            // push rbp
        0x56,                            // push rsi
        0x57,                            // push rdi
        0x41, 0x54,                      // push r12
    };
    static const char mask[] = "xxxxxxxxxxxxxxxxxxxxxxxxx";

    uintptr_t result = SigScanner::FindPattern(pat, mask, 25);
    if (result) {
        LOG("[Resolver] BRouteMsgToJob @ %p (RVA 0x%llX) via signature",
            (void*)result, (uint64_t)(result - SigScanner::GetImageBase()));
        return result;
    }

    // Fallback: string xref
    result = ResolveFuncByStringXref("CJobMgr::BRouteMsgToJob", "BRouteMsgToJob");
    return result;
}

// ── KvFindKey ─────────────────────────────────────────────────────────

static uintptr_t ResolveKvFindKey() {
    return ResolveFuncByStringXref("KeyValues::FindKey( StringView ... )", "KvFindKey");
}

// ── KvSetUint64 / KvSetInt / KvSetString ──────────────────────────────
// These all start with `test rcx, rcx; jz ...` (null check on this pointer).
// They're adjacent in the binary. Once we find one, the others are nearby.

// KvSetInt is unique at 16B (the jz offset 0x2E differs from KvSetUint64's 0x30):
//   48 85 C9  74 2E  48 89 5C 24 08  57  48 83 EC 20  8B FA
static uintptr_t ResolveKvSetInt() {
    static const uint8_t pat[] = {
        0x48, 0x85, 0xC9,              // test rcx, rcx
        0x74, 0x2E,                    // jz +2Eh
        0x48, 0x89, 0x5C, 0x24, 0x08, // mov [rsp+8], rbx
        0x57,                          // push rdi
        0x48, 0x83, 0xEC, 0x20,        // sub rsp, 20h
        0x8B, 0xFA,                    // mov edi, edx  (32-bit mov = int arg)
    };
    static const char mask[] = "xxxxxxxxxxxxxxxxx";

    uintptr_t result = SigScanner::FindPattern(pat, mask, 17);
    if (result)
        LOG("[Resolver] KvSetInt @ %p (RVA 0x%llX) via signature",
            (void*)result, (uint64_t)(result - SigScanner::GetImageBase()));
    else
        LOG("[Resolver] KvSetInt: signature not found");
    return result;
}

// KvSetString starts with `test rcx,rcx; jz` but has a 6-byte jz (0F 84 xx xx xx xx):
//   48 85 C9  0F 84 9E 00 00 00  48 89 74 24 10  57
// Wildcard the jz displacement (bytes 5-8):
static uintptr_t ResolveKvSetString() {
    static const uint8_t pat[] = {
        0x48, 0x85, 0xC9,              // test rcx, rcx
        0x0F, 0x84, 0x00, 0x00, 0x00, 0x00,  // jz near (wildcard offset)
        0x48, 0x89, 0x74, 0x24, 0x10, // mov [rsp+10h], rsi
        0x57,                          // push rdi
        0x48, 0x83, 0xEC, 0x30,        // sub rsp, 30h
    };
    static const char mask[] = "xxxxx????xxxxxxxxxx";

    uintptr_t result = SigScanner::FindPattern(pat, mask, 19);
    if (result)
        LOG("[Resolver] KvSetString @ %p (RVA 0x%llX) via signature",
            (void*)result, (uint64_t)(result - SigScanner::GetImageBase()));
    else
        LOG("[Resolver] KvSetString: signature not found");
    return result;
}

// KvSetUint64: unique with jz +30h and 64-bit mov rdi,rdx:
//   48 85 C9  74 30  48 89 5C 24 08  57  48 83 EC 20  48 8B FA
static uintptr_t ResolveKvSetUint64() {
    static const uint8_t pat[] = {
        0x48, 0x85, 0xC9,              // test rcx, rcx
        0x74, 0x30,                    // jz +30h
        0x48, 0x89, 0x5C, 0x24, 0x08, // mov [rsp+8], rbx
        0x57,                          // push rdi
        0x48, 0x83, 0xEC, 0x20,        // sub rsp, 20h
        0x48, 0x8B, 0xFA,             // mov rdi, rdx  (64-bit mov = uint64 arg)
    };
    static const char mask[] = "xxxxxxxxxxxxxxxxxx";

    uintptr_t result = SigScanner::FindPattern(pat, mask, 18);
    if (result)
        LOG("[Resolver] KvSetUint64 @ %p (RVA 0x%llX) via signature",
            (void*)result, (uint64_t)(result - SigScanner::GetImageBase()));
    else
        LOG("[Resolver] KvSetUint64: signature not found");
    return result;
}

// ── KV Getters: GetInt, GetUint64 ─────────────────────────────────────
// KvGetInt (unique 16B):
//   48 89 5C 24 10  57  48 83 EC 30  4D 85 C0  48 8D 7C 24 40
static uintptr_t ResolveKvGetInt() {
    static const uint8_t pat[] = {
        0x48, 0x89, 0x5C, 0x24, 0x10, // mov [rsp+10h], rbx
        0x57,                          // push rdi
        0x48, 0x83, 0xEC, 0x30,        // sub rsp, 30h
        0x4D, 0x85, 0xC0,             // test r8, r8
        0x48, 0x8D, 0x7C, 0x24, 0x40, // lea rdi, [rsp+40h]
    };
    static const char mask[] = "xxxxxxxxxxxxxxxxxx";

    uintptr_t result = SigScanner::FindPattern(pat, mask, 18);
    if (result)
        LOG("[Resolver] KvGetInt @ %p (RVA 0x%llX) via signature",
            (void*)result, (uint64_t)(result - SigScanner::GetImageBase()));
    else
        LOG("[Resolver] KvGetInt: signature not found");
    return result;
}

// KvGetUint64: disambiguate from KvGetInt64 via unique string xref.
static uintptr_t ResolveKvGetUint64(uintptr_t /*kvFindKeyAddr*/) {
    return ResolveFuncByStringXref(
        "can't convert int64 to uint64", "KvGetUint64");
}

// ── GetAppInfo, GetSection, ReadConfigU64 ─────────────────────────────
// GetAppInfo has a distinctive prologue: mov r8d,[rcx+68h]; mov r9d,edx; cmp r8d,0FFFFFFFFh
//   44 8B 41 68  44 8B CA  41 83 F8 FF
static uintptr_t ResolveGetAppInfo() {
    static const uint8_t pat[] = {
        0x44, 0x8B, 0x41, 0x68,       // mov r8d, [rcx+68h]
        0x44, 0x8B, 0xCA,             // mov r9d, edx
        0x41, 0x83, 0xF8, 0xFF,       // cmp r8d, 0FFFFFFFFh
    };
    static const char mask[] = "xxxxxxxxxxx";

    uintptr_t result = SigScanner::FindPattern(pat, mask, 11);
    if (result)
        LOG("[Resolver] GetAppInfo @ %p (RVA 0x%llX) via signature",
            (void*)result, (uint64_t)(result - SigScanner::GetImageBase()));
    else
        LOG("[Resolver] GetAppInfo: signature not found");
    return result;
}

// GetSection: sub rsp,28h; lea eax,[edx-2]; cmp eax,12h
//   48 83 EC 28  8D 42 FE  83 F8 12
static uintptr_t ResolveGetSection() {
    static const uint8_t pat[] = {
        0x48, 0x83, 0xEC, 0x28,       // sub rsp, 28h
        0x8D, 0x42, 0xFE,             // lea eax, [rdx-2]
        0x83, 0xF8, 0x12,             // cmp eax, 12h
    };
    static const char mask[] = "xxxxxxxxxx";

    uintptr_t result = SigScanner::FindPattern(pat, mask, 10);
    if (result)
        LOG("[Resolver] GetSection @ %p (RVA 0x%llX) via signature",
            (void*)result, (uint64_t)(result - SigScanner::GetImageBase()));
    else
        LOG("[Resolver] GetSection: signature not found");
    return result;
}

// ReadConfigU64: same prologue as an overload; take the last match after GetAppInfo.
static uintptr_t ResolveReadConfigU64(uintptr_t getAppInfoAddr) {
    static const uint8_t pat[] = {
        0x48, 0x89, 0x5C, 0x24, 0x08, // mov [rsp+8], rbx
        0x57,                          // push rdi
        0x48, 0x83, 0xEC, 0x20,        // sub rsp, 20h
        0x49, 0x8B, 0xD9,             // mov rbx, r9
        0x41, 0x8B, 0xF8,             // mov edi, r8d
    };
    static const char mask[] = "xxxxxxxxxxxxxxxx";

    if (!getAppInfoAddr) {
        // Fall back to global scan (may hit the wrong overload, but still functional)
        uintptr_t result = SigScanner::FindPattern(pat, mask, 16);
        if (result)
            LOG("[Resolver] ReadConfigU64 @ %p (RVA 0x%llX) via signature (no anchor)",
                (void*)result, (uint64_t)(result - SigScanner::GetImageBase()));
        else
            LOG("[Resolver] ReadConfigU64: signature not found");
        return result;
    }

    // Scan forward from GetAppInfo; take the last match in the window.
    uintptr_t scanStart = getAppInfoAddr + 0x80;
    size_t scanSize = 0x2000;
    uintptr_t result = 0;
    uintptr_t pos = scanStart;
    while (pos < scanStart + scanSize) {
        size_t remaining = scanStart + scanSize - pos;
        uintptr_t hit = SigScanner::FindPatternInRange(pos, remaining, pat, mask, 16);
        if (!hit) break;
        result = hit; // keep the last match
        pos = hit + 16;
    }
    if (result)
        LOG("[Resolver] ReadConfigU64 @ %p (RVA 0x%llX) via proximity to GetAppInfo",
            (void*)result, (uint64_t)(result - SigScanner::GetImageBase()));
    else
        LOG("[Resolver] ReadConfigU64: not found near GetAppInfo");
    return result;
}

// ── RefCountGlobal ────────────────────────────────────────────────────
// RefCountGlobal: second LEA target in the "client/AsyncFileIO/ReadItemsPending" function.
static uintptr_t ResolveRefCountGlobal() {
    uintptr_t funcAddr = ResolveFuncByStringXref(
        "client/AsyncFileIO/ReadItemsPending", "RefCountGlobal_anchor");
    if (!funcAddr) return 0;

    __try {
        const auto* p = reinterpret_cast<const uint8_t*>(funcAddr);
        int leaCount = 0;
        for (size_t i = 0; i + 7 <= 32; ++i) {
            if ((p[i] == 0x48 || p[i] == 0x4C) && p[i+1] == 0x8D && (p[i+2] & 0xC7) == 0x05) {
                leaCount++;
                if (leaCount == 2) { // second LEA is the one loading RefCountGlobal
                    int32_t disp = *reinterpret_cast<const int32_t*>(p + i + 3);
                    uintptr_t target = funcAddr + i + 7 + disp;
                    LOG("[Resolver] RefCountGlobal @ %p (RVA 0x%llX) via anchor func LEA",
                        (void*)target, (uint64_t)(target - SigScanner::GetImageBase()));
                    return target;
                }
            }
        }
    } __except (EXCEPTION_EXECUTE_HANDLER) {}

    LOG("[Resolver] RefCountGlobal: LEA extraction failed");
    return 0;
}

// JobCurGlobal: first mov [rip+disp], rax targeting .data in ~CJob destructor.
static uintptr_t ResolveJobCurGlobal() {
    uintptr_t funcAddr = ResolveFuncByStringXref(
        "~CJOB: %s has an unexpected threaded work item", "JobCurGlobal_anchor");
    if (!funcAddr) return 0;

    __try {
        const auto* p = reinterpret_cast<const uint8_t*>(funcAddr);
        for (size_t i = 0; i + 7 <= 0x400; ++i) {
            if (p[i] == 0x48 && p[i+1] == 0x89 && (p[i+2] & 0xC7) == 0x05) {
                int32_t disp = *reinterpret_cast<const int32_t*>(p + i + 3);
                uintptr_t target = funcAddr + i + 7 + disp;
                // Verify target is in .data section
                if (target >= SigScanner::GetDataBase() &&
                    target < SigScanner::GetDataBase() + SigScanner::GetDataSize()) {
                    LOG("[Resolver] JobCurGlobal @ %p (RVA 0x%llX) via ~CJob store",
                        (void*)target, (uint64_t)(target - SigScanner::GetImageBase()));
                    return target;
                }
            }
        }
    } __except (EXCEPTION_EXECUTE_HANDLER) {}

    LOG("[Resolver] JobCurGlobal: store extraction failed");
    return 0;
}

// ── Main resolver entry point ─────────────────────────────────────────

ResolvedAddrs Resolve(uintptr_t steamClientBase) {
    ResolvedAddrs r = {};
    memset(&r, 0, sizeof(r));

    if (!SigScanner::Init(steamClientBase)) {
        LOG("[Resolver] SigScanner::Init failed");
        return r;
    }

    LOG("[Resolver] === Beginning auto-resolution of steamclient64.dll addresses ===");

    // Phase 1: RTTI vtables (highest confidence)
    r.ccmInterfaceVtable = ResolveCCMInterfaceVtable();
    r.serviceTransportVtable = ResolveServiceTransportVtable();

    // Phase 2: AppInfo functions + engine global pointer.
    // Order matters: the CAppInfoCache offset is derived from the GetAppInfo
    // call sites, and the engine global is found via the
    // `lea reg,[reg+offset]` -> `mov reg,[rip+disp]` backwalk.
    r.getAppInfo = ResolveGetAppInfo();
    uint32_t appInfoCacheOff = DetectAppInfoCacheOffset(r.getAppInfo);
    if (!appInfoCacheOff) {
        appInfoCacheOff = 0x1208;
        LOG("[Resolver] AppInfoCache offset: falling back to 0x1208");
    }
    r.engineOffAppInfoCache = appInfoCacheOff;
    r.globalEngine = ResolveGlobalEngine(steamClientBase, appInfoCacheOff);

    // Phase 3: Protobuf helpers (signature-based)
    r.serializeToArray = ResolveSerializeToArray();
    r.parseFromArray   = ResolveParseFromArray(r.serializeToArray);

    // Phase 4: Packet routing (signature + string xref)
    r.bRouteMsgToJob = ResolveBRouteMsgToJob();
    r.wrapPacket     = ResolveWrapPacket();
    r.releaseWrapped = ResolveReleaseWrapped();
    r.refCountHelper = ResolveRefCountHelper();
    r.findJob        = ResolveFindJob();

    // Phase 5: Globals
    r.refCountGlobal = ResolveRefCountGlobal();
    r.jobCurGlobal = ResolveJobCurGlobal();

    // Phase 6: Manifest pinning (string xref)
    r.buildDepotDependency = ResolveFuncByStringXref(
        "CUserAppManager::BuildDepotDependency", "BuildDepotDependency");

    // Phase 7: Playtime functions (string xref)
    r.getAppMinutesPlayedData = ResolveFuncByStringXref(
        "CUser::GetAppMinutesPlayedData", "GetAppMinutesPlayedData");
    r.setAppLastPlayedTime = ResolveFuncByStringXref(
        "CUser::SetAppLastPlayedTime", "SetAppLastPlayedTime");
    // FlushAppMinutesPlayed has no string refs. It's adjacent to GetAppMinutesPlayedData.
    // From IDA: GetAppMinutesPlayedData=0x9BFA40, FlushAppMinutesPlayed=0x9CFEF0 (gap ~0x104B0).
    // Instead, resolve via the unique prologue. FlushAppMinutesPlayed starts with:
    //   40 55  57  41 56  48 83 EC 30  (push rbp; push rdi; push r14; sub rsp,30h)
    // followed immediately by a mov from the global engine pointer.
    // But this prologue isn't unique enough alone. We use the full 9 bytes + the fact
    // that the very next instruction loads g_pCSteamEngine (which we already resolved).
    if (r.globalEngine) {
        // Scan .text for: 40 55 57 41 56 48 83 EC 30 48 8B 05 XX XX XX XX
        // where the XX bytes, when decoded as rip+disp, point to r.globalEngine.
        static const uint8_t pat[] = {
            0x40, 0x55,              // push rbp
            0x57,                    // push rdi
            0x41, 0x56,              // push r14
            0x48, 0x83, 0xEC, 0x30, // sub rsp, 30h
            0x48, 0x8B, 0x05,       // mov rax, [rip+...]
        };
        static const char mask[] = "xxxxxxxxxxxx";
        uintptr_t scanAddr = SigScanner::GetTextBase();
        size_t remaining = SigScanner::GetTextSize();
        while (remaining >= 16) {
            uintptr_t hit = SigScanner::FindPatternInRange(scanAddr, remaining, pat, mask, 12);
            if (!hit) break;
            // Ensure 16 bytes (12 prologue + 4 displacement) fit within scan range
            size_t offset = hit - scanAddr;
            if (offset + 16 > remaining) break;
            // Verify the RIP-relative target points to globalEngine
            int32_t disp = *reinterpret_cast<const int32_t*>((const uint8_t*)hit + 12);
            uintptr_t target = hit + 16 + disp;  // instruction is 16 bytes total (12 matched + 4 disp)
            if (target == r.globalEngine) {
                r.flushAppMinutesPlayed = hit;
                LOG("[Resolver] FlushAppMinutesPlayed @ %p (RVA 0x%llX) via prologue+engine ref",
                    (void*)hit, (uint64_t)(hit - steamClientBase));
                break;
            }
            // Advance past this match
            scanAddr = hit + 16;
            remaining -= (offset + 16);
        }
    }
    if (!r.flushAppMinutesPlayed)
        LOG("[Resolver] FlushAppMinutesPlayed: not resolved");

    // Phase 8: KV functions (signature-based, some anchored to KvFindKey)
    r.kvFindKey    = ResolveKvFindKey();
    r.kvGetUint64  = ResolveKvGetUint64(r.kvFindKey);
    r.kvGetInt     = ResolveKvGetInt();
    r.kvSetUint64  = ResolveKvSetUint64();
    r.kvSetInt     = ResolveKvSetInt();
    r.kvSetString  = ResolveKvSetString();

    // Phase 9: AppInfo functions (getAppInfo resolved in Phase 2;
    // ReadConfigU64 anchored to it)
    r.getSection     = ResolveGetSection();
    r.readConfigU64  = ResolveReadConfigU64(r.getAppInfo);

    // Phase 10: BAsyncSend (string xref — unique "CProtoBufMsg::BAsyncSend")
    r.bAsyncSend = ResolveFuncByStringXref(
        "CProtoBufMsg::BAsyncSend", "BAsyncSend");

    // Phase 11: PlaytimeWriter — first E8 call after LEA to the handler string.
    {
        const char* handlerStr = "Player.ClientGetLastPlayedTimes#1";
        size_t handlerLen = strlen(handlerStr);
        char hmask[64];
        memset(hmask, 'x', handlerLen);
        hmask[handlerLen] = '\0';

        uintptr_t hStrAddr = SigScanner::FindPatternInRange(
            SigScanner::GetRdataBase(), SigScanner::GetRdataSize(),
            (const uint8_t*)handlerStr, hmask, handlerLen);
        if (hStrAddr) {
            const auto* text = reinterpret_cast<const uint8_t*>(SigScanner::GetTextBase());
            size_t textSize = SigScanner::GetTextSize();
            __try {
                for (size_t i = 0; i + 7 <= textSize; ++i) {
                    if ((text[i] == 0x48 || text[i] == 0x4C) && text[i+1] == 0x8D &&
                        (text[i+2] & 0xC7) == 0x05) {
                        uintptr_t instrAddr = SigScanner::GetTextBase() + i;
                        int32_t disp = *reinterpret_cast<const int32_t*>(text + i + 3);
                        if (instrAddr + 7 + disp != hStrAddr) continue;

                        // Found the LEA to the handler string. Scan forward for first E8 call.
                        for (size_t j = i + 7; j + 5 <= textSize; ++j) {
                            if (text[j] == 0xE8) {
                                int32_t callDisp = *reinterpret_cast<const int32_t*>(text + j + 1);
                                uintptr_t target = SigScanner::GetTextBase() + j + 5 + callDisp;
                                if (target >= SigScanner::GetImageBase() &&
                                    target < SigScanner::GetImageBase() + SigScanner::GetImageSize()) {
                                    r.playtimeWriter = target;
                                    LOG("[Resolver] PlaytimeWriter @ %p (RVA 0x%llX) via GetLastPlayedTimes handler call",
                                        (void*)target, (uint64_t)(target - steamClientBase));
                                    break;
                                }
                            }
                        }
                        break;
                    }
                }
            } __except (EXCEPTION_EXECUTE_HANDLER) {}
        }
        if (!r.playtimeWriter)
            LOG("[Resolver] PlaytimeWriter: not resolved");
    }

    // Phase 12: PbMsgCtor — loads CProtoBufMsgBase vtable via RTTI, stores to [rcx],
    // and has `mov [rcx+38h], r8d` (44 89 41 38) at +0x0A.
    {
        uintptr_t baseMsgVtable = SigScanner::ResolveVtableByRtti(".?AVCProtoBufMsgBase@@");
        if (baseMsgVtable) {
            // PbMsgCtor: sub rsp,30h then LEA rax, CProtoBufMsgBase_vt; mov [rcx], rax
            // Build 11.12.30.07 prologue (base ctor 0xD1C350):
            //   mov [rsp+8],rbx ; push rdi ; sub rsp,30h ; mov rdi,rcx
            //   ; mov byte [rsp+28h],1 ; or edx,80000000h ; mov byte [rsp+20h],0
            static const uint8_t pat[] = {
                0x48, 0x89, 0x5C, 0x24, 0x08,        // mov [rsp+8], rbx
                0x57,                                 // push rdi
                0x48, 0x83, 0xEC, 0x30,               // sub rsp, 30h
                0x48, 0x8B, 0xF9,                     // mov rdi, rcx
                0xC6, 0x44, 0x24, 0x28, 0x01,         // mov byte [rsp+28h], 1
                0x81, 0xCA, 0x00, 0x00, 0x00, 0x80,   // or edx, 80000000h
            };
            static const char mask[] = "xxxxxxxxxxxxxxxxxxxxxxx";
            uintptr_t hit = SigScanner::FindPattern(pat, mask, 23);
            if (hit) {
                // Verify it LEAs the CProtoBufMsgBase vtable within the next 0x18 bytes
                uintptr_t leaTarget = SigScanner::FindFirstRipRelLeaTarget(hit + 12, 0x18);
                if (leaTarget == baseMsgVtable) {
                    r.pbMsgCtor = hit;
                    LOG("[Resolver] PbMsgCtor @ %p (RVA 0x%llX) via signature + vtable verify",
                        (void*)hit, (uint64_t)(hit - steamClientBase));
                }
            }
            if (!r.pbMsgCtor)
                LOG("[Resolver] PbMsgCtor: not resolved");

            // Phase 13: PbMsgCleanup — build 11.12.30.07 destructor (0xD1C760):
            //   48 89 5C 24 08 57 48 83 EC 20 80 79 19 00 48 8D 05 <disp> 48 89 01 48 8B D9
            //   mov [rsp+8],rbx ; push rdi ; sub rsp,20h ; cmp byte [rcx+19h],0
            //   ; lea rax,[rip+CProtoBufMsgBase_vt] ; mov [rcx],rax ; mov rbx,rcx
            // Verify the LEA target == baseMsgVtable.
            const auto* text = reinterpret_cast<const uint8_t*>(SigScanner::GetTextBase());
            size_t textSize = SigScanner::GetTextSize();
            static const uint8_t cpat[] = {
                0x48, 0x89, 0x5C, 0x24, 0x08, 0x57, 0x48, 0x83, 0xEC, 0x20,
                0x80, 0x79, 0x19, 0x00, 0x48, 0x8D, 0x05,
            };
            __try {
                for (size_t i = 0; i + 21 <= textSize; ++i) {
                    if (memcmp(text + i, cpat, 17) == 0) {
                        uintptr_t instrAddr = SigScanner::GetTextBase() + i + 14;
                        int32_t disp = *reinterpret_cast<const int32_t*>(text + i + 17);
                        uintptr_t target = instrAddr + 7 + disp;
                        if (target == baseMsgVtable) {
                            r.pbMsgCleanup = SigScanner::GetTextBase() + i;
                            LOG("[Resolver] PbMsgCleanup @ %p (RVA 0x%llX) via prologue + vtable LEA",
                                (void*)r.pbMsgCleanup, (uint64_t)(r.pbMsgCleanup - steamClientBase));
                            break;
                        }
                    }
                }
            } __except (EXCEPTION_EXECUTE_HANDLER) {}
            if (!r.pbMsgCleanup)
                LOG("[Resolver] PbMsgCleanup: not resolved");
        } else {
            LOG("[Resolver] PbMsgCtor/Cleanup: CProtoBufMsgBase RTTI not found");
        }
    }

    // Phase 14: PbMsgFinalize — string xref "!m_pProtoBufBody" + cmp [rcx+30h] guard.
    {
        const char* searchStr = "!m_pProtoBufBody";
        size_t searchLen = strlen(searchStr);
        char mask[128];
        memset(mask, 'x', searchLen);
        mask[searchLen] = '\0';

        uintptr_t strAddr = SigScanner::FindPatternInRange(
            SigScanner::GetRdataBase(), SigScanner::GetRdataSize(),
            (const uint8_t*)searchStr, mask, searchLen);

        r.pbMsgFinalize = 0;
        if (strAddr) {
            const auto* text = reinterpret_cast<const uint8_t*>(SigScanner::GetTextBase());
            size_t textSize = SigScanner::GetTextSize();
            // Check bytes: 48 83 79 38 00 = cmp qword ptr [rcx+38h], 0
            // (build 11.12.30.07: the protobuf body lives at +0x38, was +0x30)
            static const uint8_t cmpPat[] = { 0x48, 0x83, 0x79, 0x38, 0x00 };

            __try {
                for (size_t i = 0; i + 7 <= textSize; ++i) {
                    if ((text[i] == 0x48 || text[i] == 0x4C) && text[i+1] == 0x8D &&
                        (text[i+2] & 0xC7) == 0x05) {
                        uintptr_t instrAddr = SigScanner::GetTextBase() + i;
                        int32_t disp = *reinterpret_cast<const int32_t*>(text + i + 3);
                        uintptr_t refTarget = instrAddr + 7 + disp;
                        if (refTarget != strAddr) continue;

                        // Found LEA to "!m_pProtoBufBody". Walk back to function start.
                        for (int back = 0; back < 0x80; back++) {
                            uintptr_t candidate = instrAddr - back;
                            if (candidate < SigScanner::GetTextBase()) break;
                            if (!SigScanner::LooksLikeFunctionStart(candidate)) continue;

                            // Verify: cmp [rcx+30h], 0 within first 13 bytes (prologue + guard)
                            const uint8_t* fn = reinterpret_cast<const uint8_t*>(candidate);
                            bool hasCmp = false;
                            for (int off = 0; off <= 8; off++) {
                                if (memcmp(fn + off, cmpPat, 5) == 0) { hasCmp = true; break; }
                            }
                            if (!hasCmp) break; // wrong function, try next xref

                            r.pbMsgFinalize = candidate;
                            break;
                        }
                        if (r.pbMsgFinalize) break;
                    }
                }
            } __except (EXCEPTION_EXECUTE_HANDLER) {}
        }

        if (r.pbMsgFinalize)
            LOG("[Resolver] PbMsgFinalize @ %p (RVA 0x%llX) via string xref + cmp guard",
                (void*)r.pbMsgFinalize, (uint64_t)(r.pbMsgFinalize - steamClientBase));
        else
            LOG("[Resolver] PbMsgFinalize: not resolved");
    }

    // Phase 14b: CProtoBufMsg layout offsets (dynamic) -- derived from the
    // base ctor's 0xFFFFFFFF connection-handle init, cross-checked with the
    // finalize guard. Falls back to defaults in the consumer if undetected.
    {
        CpbLayout lay;
        if (DetectCProtoBufMsgLayout(r.pbMsgCtor, r.pbMsgFinalize, lay)) {
            r.cpbConnOff = lay.conn;
            r.cpbEmsgOff = lay.emsg;
            r.cpbHdrOff  = lay.hdr;
            r.cpbBodyOff = lay.body;
        } else {
            LOG("[Resolver] CProtoBufMsg layout: detection failed, consumer will use defaults");
        }
    }

    // Phase 15: YieldIfTimeSlice — prologue + cmp rcx, [rip+g_pJobCur]
    if (r.jobCurGlobal) {
        static const uint8_t pat[] = {
            0x48, 0x89, 0x5C, 0x24, 0x08, // mov [rsp+8], rbx
            0x48, 0x89, 0x74, 0x24, 0x10, // mov [rsp+10h], rsi
            0x57,                          // push rdi
            0x48, 0x83, 0xEC, 0x20,        // sub rsp, 20h
            0x48, 0x3B, 0x0D,              // cmp rcx, [rip+...]
        };
        static const char mask[] = "xxxxxxxxxxxxxxxxxx";
        uintptr_t scanAddr = SigScanner::GetTextBase();
        size_t remaining = SigScanner::GetTextSize();
        while (remaining > 22) {
            uintptr_t hit = SigScanner::FindPatternInRange(scanAddr, remaining, pat, mask, 18);
            if (!hit) break;
            // Verify the RIP-relative target is g_pJobCur
            int32_t disp = *reinterpret_cast<const int32_t*>((const uint8_t*)hit + 18);
            uintptr_t target = hit + 22 + disp;  // instr at +15 is 7 bytes (48 3B 0D xx xx xx xx)
            if (target == r.jobCurGlobal) {
                r.yieldIfTimeSlice = hit;
                LOG("[Resolver] YieldIfTimeSlice @ %p (RVA 0x%llX) via prologue + g_pJobCur ref",
                    (void*)hit, (uint64_t)(hit - steamClientBase));
                break;
            }
            size_t consumed = (hit - scanAddr) + 18;
            scanAddr = hit + 18;
            remaining -= consumed;
        }
        if (!r.yieldIfTimeSlice)
            LOG("[Resolver] YieldIfTimeSlice: not resolved");
    } else {
        LOG("[Resolver] YieldIfTimeSlice: skipped (jobCurGlobal not resolved)");
    }

    // Phase 16: RTTI vtables for protobuf message wrappers
    r.getUserStatsVtable = SigScanner::ResolveVtableByRtti(
        ".?AV?$CProtoBufMsg@VCMsgClientGetUserStats@@@@");
    if (r.getUserStatsVtable)
        LOG("[Resolver] GetUserStatsVtable @ %p (RVA 0x%llX) via RTTI",
            (void*)r.getUserStatsVtable, (uint64_t)(r.getUserStatsVtable - steamClientBase));
    else
        LOG("[Resolver] GetUserStatsVtable: RTTI not found");

    r.respWrapperVtable = SigScanner::ResolveVtableByRtti(
        ".?AV?$CProtoBufMsg@VCPlayer_GetLastPlayedTimes_Response@@@@");
    if (r.respWrapperVtable)
        LOG("[Resolver] RespWrapperVtable @ %p (RVA 0x%llX) via RTTI",
            (void*)r.respWrapperVtable, (uint64_t)(r.respWrapperVtable - steamClientBase));
    else
        LOG("[Resolver] RespWrapperVtable: RTTI not found");

    // Phase 17: Descriptor pointers (vtable ptr in .data/.rdata).
    {
        // GetUserStatsDesc: find QWORD in .rdata/.data pointing to CMsgClientGetUserStats vtable
        uintptr_t msgVtable = SigScanner::ResolveVtableByRtti(".?AVCMsgClientGetUserStats@@");
        if (msgVtable) {
            // Scan .data then .rdata for a QWORD containing this vtable address
            auto scanForPtr = [&](uintptr_t sectionBase, size_t sectionSize) -> uintptr_t {
                const auto* mem = reinterpret_cast<const uint8_t*>(sectionBase);
                for (size_t i = 0; i + 8 <= sectionSize; i += 8) {
                    if (*reinterpret_cast<const uintptr_t*>(mem + i) == msgVtable)
                        return sectionBase + i;
                }
                return 0;
            };
            r.getUserStatsDesc = scanForPtr(SigScanner::GetDataBase(), SigScanner::GetDataSize());
            if (!r.getUserStatsDesc)
                r.getUserStatsDesc = scanForPtr(SigScanner::GetRdataBase(), SigScanner::GetRdataSize());
            if (r.getUserStatsDesc)
                LOG("[Resolver] GetUserStatsDesc @ %p (RVA 0x%llX) via vtable-ptr scan",
                    (void*)r.getUserStatsDesc, (uint64_t)(r.getUserStatsDesc - steamClientBase));
            else
                LOG("[Resolver] GetUserStatsDesc: vtable pointer not found in .data/.rdata");
        } else {
            LOG("[Resolver] GetUserStatsDesc: CMsgClientGetUserStats RTTI not found");
        }

        // RespDescriptor: same for CPlayer_GetLastPlayedTimes_Response
        uintptr_t respVtable = SigScanner::ResolveVtableByRtti(".?AVCPlayer_GetLastPlayedTimes_Response@@");
        if (respVtable) {
            auto scanForPtr = [&](uintptr_t sectionBase, size_t sectionSize) -> uintptr_t {
                const auto* mem = reinterpret_cast<const uint8_t*>(sectionBase);
                for (size_t i = 0; i + 8 <= sectionSize; i += 8) {
                    if (*reinterpret_cast<const uintptr_t*>(mem + i) == respVtable)
                        return sectionBase + i;
                }
                return 0;
            };
            r.respDescriptor = scanForPtr(SigScanner::GetDataBase(), SigScanner::GetDataSize());
            if (!r.respDescriptor)
                r.respDescriptor = scanForPtr(SigScanner::GetRdataBase(), SigScanner::GetRdataSize());
            if (r.respDescriptor)
                LOG("[Resolver] RespDescriptor @ %p (RVA 0x%llX) via vtable-ptr scan",
                    (void*)r.respDescriptor, (uint64_t)(r.respDescriptor - steamClientBase));
            else
                LOG("[Resolver] RespDescriptor: vtable pointer not found in .data/.rdata");
        } else {
            LOG("[Resolver] RespDescriptor: CPlayer_GetLastPlayedTimes_Response RTTI not found");
        }
    }

    // Phase 18: RegKeySyncTime — string ptr scan, synthetic slot fallback.
    {
        const char needle[] = "LastPlayedTimesSyncTime";
        size_t needleLen = sizeof(needle) - 1;
        char nmask[32];
        memset(nmask, 'x', needleLen);
        nmask[needleLen] = '\0';

        uintptr_t strAddr = SigScanner::FindPatternInRange(
            SigScanner::GetRdataBase(), SigScanner::GetRdataSize(),
            (const uint8_t*)needle, nmask, needleLen);
        if (!strAddr) strAddr = SigScanner::FindPatternInRange(
            SigScanner::GetDataBase(), SigScanner::GetDataSize(),
            (const uint8_t*)needle, nmask, needleLen);
        if (strAddr) {
            // The needle may match inside a longer string (e.g.
            // "Software\Valve\Steam\LastPlayedTimesSyncTime"). Walk backward to
            // the containing C-string's start for the pointer search.
            {
                const uint8_t* p = reinterpret_cast<const uint8_t*>(strAddr);
                const uint8_t* modBase = reinterpret_cast<const uint8_t*>(steamClientBase);
                while (p > modBase && *(p - 1) != 0) { p--; strAddr--; }
                LOG("[Resolver] RegKeySyncTime: needle in containing string at RVA 0x%llX: \"%.80s\"",
                    (uint64_t)(strAddr - steamClientBase), (const char*)strAddr);
            }
            // Find the QWORD pointer to this string in .data/.rdata
            auto scanForPtr = [&](uintptr_t sectionBase, size_t sectionSize) -> uintptr_t {
                const auto* mem = reinterpret_cast<const uint8_t*>(sectionBase);
                for (size_t i = 0; i + 8 <= sectionSize; i += 8) {
                    if (*reinterpret_cast<const uintptr_t*>(mem + i) == strAddr)
                        return sectionBase + i;
                }
                return 0;
            };
            r.regKeySyncTime = scanForPtr(SigScanner::GetDataBase(), SigScanner::GetDataSize());
            if (!r.regKeySyncTime)
                r.regKeySyncTime = scanForPtr(SigScanner::GetRdataBase(), SigScanner::GetRdataSize());
            if (r.regKeySyncTime) {
                LOG("[Resolver] RegKeySyncTime @ %p (RVA 0x%llX) via string-ptr scan",
                    (void*)r.regKeySyncTime, (uint64_t)(r.regKeySyncTime - steamClientBase));
            } else {
                // Newer builds: no absolute pointer in data sections (LEA-referenced).
                // Synthesize a stable slot that dereferences to the string address.
                static uintptr_t s_syntheticSlot = 0;
                s_syntheticSlot = strAddr;
                r.regKeySyncTime = (uintptr_t)&s_syntheticSlot;
                LOG("[Resolver] RegKeySyncTime @ %p (synthetic, string at RVA 0x%llX)",
                    (void*)r.regKeySyncTime, (uint64_t)(strAddr - steamClientBase));
            }
        } else {
            LOG("[Resolver] RegKeySyncTime: 'LastPlayedTimesSyncTime' string not found");
        }
    }

    // Phase 19: Struct offsets (leave at 0 -- use hardcoded fallbacks for now)
    r.engineOffJobMgr       = 0;
    r.engineOffGlobalHandle = 0;
    r.engineOffUserMap      = 0;
    r.ccmOffConnContext     = 0;
    r.userOffCcmInterface   = 0;
    // engineOffAppInfoCache is derived dynamically in Phase 2.

    LOG("[Resolver] === Auto-resolution complete ===");
    return r;
}

void LogComparison(const ResolvedAddrs& r, uintptr_t base) {
    LOG("[Resolver] === Comparison (resolved RVA vs expected) ===");

    int total = 0, matched = 0, failed = 0;
    auto logEntry = [&](const char* name, uintptr_t resolved, uintptr_t expectedRva) {
        total++;
        if (resolved) {
            uintptr_t resolvedRva = resolved - base;
            bool match = (resolvedRva == expectedRva);
            if (match) matched++;
            LOG("[Resolver]   %-30s 0x%llX  %s",
                name, (uint64_t)resolvedRva, match ? "OK" : "MISMATCH");
        } else {
            failed++;
            LOG("[Resolver]   %-30s FAILED (expected 0x%llX)", name, (uint64_t)expectedRva);
        }
    };

    // Expected RVAs for steamclient64.dll build 11.12.30.07 (Steam version 1791918634).
    // Update these whenever the target build changes so genuine resolver drift is
    // reported as MISMATCH instead of being masked by stale values.
    logEntry("CCMInterface VT",        r.ccmInterfaceVtable,      0x12B4AE8);
    logEntry("ServiceTransport VT",    r.serviceTransportVtable,  0x1292150);
    logEntry("GlobalEngine",           r.globalEngine,            0x181D008);
    logEntry("ParseFromArray",         r.parseFromArray,          0xBEEC40);
    logEntry("SerializeToArray",       r.serializeToArray,        0xBEF050);
    logEntry("WrapPacket",             r.wrapPacket,              0xD24E40);
    logEntry("BRouteMsgToJob",         r.bRouteMsgToJob,          0xD30A10);
    logEntry("ReleaseWrapped",         r.releaseWrapped,          0x0ED4A0);
    logEntry("RefCountHelper",         r.refCountHelper,          0xDEFBC0);
    logEntry("FindJob",                r.findJob,                 0xD33600);
    logEntry("RefCountGlobal",         r.refCountGlobal,          0x18083D8);
    logEntry("JobCurGlobal",           r.jobCurGlobal,            0x183A5B0);
    logEntry("BuildDepotDependency",   r.buildDepotDependency,    0x4D75C0);
    logEntry("GetAppMinutesPlayed",    r.getAppMinutesPlayedData, 0x9E2510);
    logEntry("FlushAppMinutesPlayed",  r.flushAppMinutesPlayed,   0x9F2C20);
    logEntry("SetAppLastPlayedTime",   r.setAppLastPlayedTime,    0x9F5A50);
    logEntry("KvFindKey",              r.kvFindKey,               0xD27910);
    logEntry("KvGetUint64",            r.kvGetUint64,             0xD28CC0);
    logEntry("KvGetInt",               r.kvGetInt,                0xD28870);
    logEntry("KvSetUint64",            r.kvSetUint64,             0xD28F30);
    logEntry("KvSetInt",               r.kvSetInt,                0xD28F70);
    logEntry("KvSetString",            r.kvSetString,             0xD28FB0);
    logEntry("GetAppInfo",             r.getAppInfo,              0x4C8440);
    logEntry("GetSection",             r.getSection,              0x4CA770);
    logEntry("ReadConfigU64",          r.readConfigU64,           0x4C94B0);
    logEntry("BAsyncSend",             r.bAsyncSend,              0xD1CBB0);
    logEntry("PlaytimeWriter",         r.playtimeWriter,          0x9EED70);
    logEntry("PbMsgCtor",              r.pbMsgCtor,               0xD1C350);
    logEntry("PbMsgFinalize",          r.pbMsgFinalize,           0xD21D50);
    logEntry("PbMsgCleanup",           r.pbMsgCleanup,            0xD1C760);
    logEntry("YieldIfTimeSlice",       r.yieldIfTimeSlice,        0xD118B0);
    logEntry("GetUserStatsVtable",     r.getUserStatsVtable,      0x13841A8);
    logEntry("GetUserStatsDesc",       r.getUserStatsDesc,        0x173E9A0);
    logEntry("RespWrapperVtable",      r.respWrapperVtable,       0x1370C50);
    logEntry("RespDescriptor",         r.respDescriptor,          0x171AEF0);
    logEntry("RegKeySyncTime",         r.regKeySyncTime,          0x172DE68);

    LOG("[Resolver] Result: %d/%d matched, %d failed", matched, total, failed);
}

} // namespace ScResolver
