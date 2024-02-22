// Code generated by go tool dist; DO NOT EDIT.
// This is a bootstrap copy of /Users/litiantian/code/m_code/read_go_code/go_source/go/src/cmd/internal/obj/x86/anames.go

//line /Users/litiantian/code/m_code/read_go_code/go_source/go/src/cmd/internal/obj/x86/anames.go:1
// Code generated by stringer -i aenum.go -o anames.go -p x86; DO NOT EDIT.

package x86

import "bootstrap/cmd/internal/obj"

var Anames = []string{
	obj.A_ARCHSPECIFIC: "AAA",
	"AAD",
	"AAM",
	"AAS",
	"ADCB",
	"ADCL",
	"ADCQ",
	"ADCW",
	"ADCXL",
	"ADCXQ",
	"ADDB",
	"ADDL",
	"ADDPD",
	"ADDPS",
	"ADDQ",
	"ADDSD",
	"ADDSS",
	"ADDSUBPD",
	"ADDSUBPS",
	"ADDW",
	"ADJSP",
	"ADOXL",
	"ADOXQ",
	"AESDEC",
	"AESDECLAST",
	"AESENC",
	"AESENCLAST",
	"AESIMC",
	"AESKEYGENASSIST",
	"ANDB",
	"ANDL",
	"ANDNL",
	"ANDNPD",
	"ANDNPS",
	"ANDNQ",
	"ANDPD",
	"ANDPS",
	"ANDQ",
	"ANDW",
	"ARPL",
	"BEXTRL",
	"BEXTRQ",
	"BLENDPD",
	"BLENDPS",
	"BLENDVPD",
	"BLENDVPS",
	"BLSIL",
	"BLSIQ",
	"BLSMSKL",
	"BLSMSKQ",
	"BLSRL",
	"BLSRQ",
	"BOUNDL",
	"BOUNDW",
	"BSFL",
	"BSFQ",
	"BSFW",
	"BSRL",
	"BSRQ",
	"BSRW",
	"BSWAPL",
	"BSWAPQ",
	"BTCL",
	"BTCQ",
	"BTCW",
	"BTL",
	"BTQ",
	"BTRL",
	"BTRQ",
	"BTRW",
	"BTSL",
	"BTSQ",
	"BTSW",
	"BTW",
	"BYTE",
	"BZHIL",
	"BZHIQ",
	"CBW",
	"CDQ",
	"CDQE",
	"CLAC",
	"CLC",
	"CLD",
	"CLDEMOTE",
	"CLFLUSH",
	"CLFLUSHOPT",
	"CLI",
	"CLTS",
	"CLWB",
	"CMC",
	"CMOVLCC",
	"CMOVLCS",
	"CMOVLEQ",
	"CMOVLGE",
	"CMOVLGT",
	"CMOVLHI",
	"CMOVLLE",
	"CMOVLLS",
	"CMOVLLT",
	"CMOVLMI",
	"CMOVLNE",
	"CMOVLOC",
	"CMOVLOS",
	"CMOVLPC",
	"CMOVLPL",
	"CMOVLPS",
	"CMOVQCC",
	"CMOVQCS",
	"CMOVQEQ",
	"CMOVQGE",
	"CMOVQGT",
	"CMOVQHI",
	"CMOVQLE",
	"CMOVQLS",
	"CMOVQLT",
	"CMOVQMI",
	"CMOVQNE",
	"CMOVQOC",
	"CMOVQOS",
	"CMOVQPC",
	"CMOVQPL",
	"CMOVQPS",
	"CMOVWCC",
	"CMOVWCS",
	"CMOVWEQ",
	"CMOVWGE",
	"CMOVWGT",
	"CMOVWHI",
	"CMOVWLE",
	"CMOVWLS",
	"CMOVWLT",
	"CMOVWMI",
	"CMOVWNE",
	"CMOVWOC",
	"CMOVWOS",
	"CMOVWPC",
	"CMOVWPL",
	"CMOVWPS",
	"CMPB",
	"CMPL",
	"CMPPD",
	"CMPPS",
	"CMPQ",
	"CMPSB",
	"CMPSD",
	"CMPSL",
	"CMPSQ",
	"CMPSS",
	"CMPSW",
	"CMPW",
	"CMPXCHG16B",
	"CMPXCHG8B",
	"CMPXCHGB",
	"CMPXCHGL",
	"CMPXCHGQ",
	"CMPXCHGW",
	"COMISD",
	"COMISS",
	"CPUID",
	"CQO",
	"CRC32B",
	"CRC32L",
	"CRC32Q",
	"CRC32W",
	"CVTPD2PL",
	"CVTPD2PS",
	"CVTPL2PD",
	"CVTPL2PS",
	"CVTPS2PD",
	"CVTPS2PL",
	"CVTSD2SL",
	"CVTSD2SQ",
	"CVTSD2SS",
	"CVTSL2SD",
	"CVTSL2SS",
	"CVTSQ2SD",
	"CVTSQ2SS",
	"CVTSS2SD",
	"CVTSS2SL",
	"CVTSS2SQ",
	"CVTTPD2PL",
	"CVTTPS2PL",
	"CVTTSD2SL",
	"CVTTSD2SQ",
	"CVTTSS2SL",
	"CVTTSS2SQ",
	"CWD",
	"CWDE",
	"DAA",
	"DAS",
	"DECB",
	"DECL",
	"DECQ",
	"DECW",
	"DIVB",
	"DIVL",
	"DIVPD",
	"DIVPS",
	"DIVQ",
	"DIVSD",
	"DIVSS",
	"DIVW",
	"DPPD",
	"DPPS",
	"EMMS",
	"ENTER",
	"EXTRACTPS",
	"F2XM1",
	"FABS",
	"FADDD",
	"FADDDP",
	"FADDF",
	"FADDL",
	"FADDW",
	"FBLD",
	"FBSTP",
	"FCHS",
	"FCLEX",
	"FCMOVB",
	"FCMOVBE",
	"FCMOVCC",
	"FCMOVCS",
	"FCMOVE",
	"FCMOVEQ",
	"FCMOVHI",
	"FCMOVLS",
	"FCMOVNB",
	"FCMOVNBE",
	"FCMOVNE",
	"FCMOVNU",
	"FCMOVU",
	"FCMOVUN",
	"FCOMD",
	"FCOMDP",
	"FCOMDPP",
	"FCOMF",
	"FCOMFP",
	"FCOMI",
	"FCOMIP",
	"FCOML",
	"FCOMLP",
	"FCOMW",
	"FCOMWP",
	"FCOS",
	"FDECSTP",
	"FDIVD",
	"FDIVDP",
	"FDIVF",
	"FDIVL",
	"FDIVRD",
	"FDIVRDP",
	"FDIVRF",
	"FDIVRL",
	"FDIVRW",
	"FDIVW",
	"FFREE",
	"FINCSTP",
	"FINIT",
	"FLD1",
	"FLDCW",
	"FLDENV",
	"FLDL2E",
	"FLDL2T",
	"FLDLG2",
	"FLDLN2",
	"FLDPI",
	"FLDZ",
	"FMOVB",
	"FMOVBP",
	"FMOVD",
	"FMOVDP",
	"FMOVF",
	"FMOVFP",
	"FMOVL",
	"FMOVLP",
	"FMOVV",
	"FMOVVP",
	"FMOVW",
	"FMOVWP",
	"FMOVX",
	"FMOVXP",
	"FMULD",
	"FMULDP",
	"FMULF",
	"FMULL",
	"FMULW",
	"FNOP",
	"FPATAN",
	"FPREM",
	"FPREM1",
	"FPTAN",
	"FRNDINT",
	"FRSTOR",
	"FSAVE",
	"FSCALE",
	"FSIN",
	"FSINCOS",
	"FSQRT",
	"FSTCW",
	"FSTENV",
	"FSTSW",
	"FSUBD",
	"FSUBDP",
	"FSUBF",
	"FSUBL",
	"FSUBRD",
	"FSUBRDP",
	"FSUBRF",
	"FSUBRL",
	"FSUBRW",
	"FSUBW",
	"FTST",
	"FUCOM",
	"FUCOMI",
	"FUCOMIP",
	"FUCOMP",
	"FUCOMPP",
	"FXAM",
	"FXCHD",
	"FXRSTOR",
	"FXRSTOR64",
	"FXSAVE",
	"FXSAVE64",
	"FXTRACT",
	"FYL2X",
	"FYL2XP1",
	"HADDPD",
	"HADDPS",
	"HLT",
	"HSUBPD",
	"HSUBPS",
	"ICEBP",
	"IDIVB",
	"IDIVL",
	"IDIVQ",
	"IDIVW",
	"IMUL3L",
	"IMUL3Q",
	"IMUL3W",
	"IMULB",
	"IMULL",
	"IMULQ",
	"IMULW",
	"INB",
	"INCB",
	"INCL",
	"INCQ",
	"INCW",
	"INL",
	"INSB",
	"INSERTPS",
	"INSL",
	"INSW",
	"INT",
	"INTO",
	"INVD",
	"INVLPG",
	"INVPCID",
	"INW",
	"IRETL",
	"IRETQ",
	"IRETW",
	"JCC",
	"JCS",
	"JCXZL",
	"JCXZQ",
	"JCXZW",
	"JEQ",
	"JGE",
	"JGT",
	"JHI",
	"JLE",
	"JLS",
	"JLT",
	"JMI",
	"JNE",
	"JOC",
	"JOS",
	"JPC",
	"JPL",
	"JPS",
	"KADDB",
	"KADDD",
	"KADDQ",
	"KADDW",
	"KANDB",
	"KANDD",
	"KANDNB",
	"KANDND",
	"KANDNQ",
	"KANDNW",
	"KANDQ",
	"KANDW",
	"KMOVB",
	"KMOVD",
	"KMOVQ",
	"KMOVW",
	"KNOTB",
	"KNOTD",
	"KNOTQ",
	"KNOTW",
	"KORB",
	"KORD",
	"KORQ",
	"KORTESTB",
	"KORTESTD",
	"KORTESTQ",
	"KORTESTW",
	"KORW",
	"KSHIFTLB",
	"KSHIFTLD",
	"KSHIFTLQ",
	"KSHIFTLW",
	"KSHIFTRB",
	"KSHIFTRD",
	"KSHIFTRQ",
	"KSHIFTRW",
	"KTESTB",
	"KTESTD",
	"KTESTQ",
	"KTESTW",
	"KUNPCKBW",
	"KUNPCKDQ",
	"KUNPCKWD",
	"KXNORB",
	"KXNORD",
	"KXNORQ",
	"KXNORW",
	"KXORB",
	"KXORD",
	"KXORQ",
	"KXORW",
	"LAHF",
	"LARL",
	"LARQ",
	"LARW",
	"LDDQU",
	"LDMXCSR",
	"LEAL",
	"LEAQ",
	"LEAVEL",
	"LEAVEQ",
	"LEAVEW",
	"LEAW",
	"LFENCE",
	"LFSL",
	"LFSQ",
	"LFSW",
	"LGDT",
	"LGSL",
	"LGSQ",
	"LGSW",
	"LIDT",
	"LLDT",
	"LMSW",
	"LOCK",
	"LODSB",
	"LODSL",
	"LODSQ",
	"LODSW",
	"LONG",
	"LOOP",
	"LOOPEQ",
	"LOOPNE",
	"LSLL",
	"LSLQ",
	"LSLW",
	"LSSL",
	"LSSQ",
	"LSSW",
	"LTR",
	"LZCNTL",
	"LZCNTQ",
	"LZCNTW",
	"MASKMOVOU",
	"MASKMOVQ",
	"MAXPD",
	"MAXPS",
	"MAXSD",
	"MAXSS",
	"MFENCE",
	"MINPD",
	"MINPS",
	"MINSD",
	"MINSS",
	"MONITOR",
	"MOVAPD",
	"MOVAPS",
	"MOVB",
	"MOVBEL",
	"MOVBEQ",
	"MOVBEW",
	"MOVBLSX",
	"MOVBLZX",
	"MOVBQSX",
	"MOVBQZX",
	"MOVBWSX",
	"MOVBWZX",
	"MOVDDUP",
	"MOVHLPS",
	"MOVHPD",
	"MOVHPS",
	"MOVL",
	"MOVLHPS",
	"MOVLPD",
	"MOVLPS",
	"MOVLQSX",
	"MOVLQZX",
	"MOVMSKPD",
	"MOVMSKPS",
	"MOVNTDQA",
	"MOVNTIL",
	"MOVNTIQ",
	"MOVNTO",
	"MOVNTPD",
	"MOVNTPS",
	"MOVNTQ",
	"MOVO",
	"MOVOU",
	"MOVQ",
	"MOVQL",
	"MOVQOZX",
	"MOVSB",
	"MOVSD",
	"MOVSHDUP",
	"MOVSL",
	"MOVSLDUP",
	"MOVSQ",
	"MOVSS",
	"MOVSW",
	"MOVSWW",
	"MOVUPD",
	"MOVUPS",
	"MOVW",
	"MOVWLSX",
	"MOVWLZX",
	"MOVWQSX",
	"MOVWQZX",
	"MOVZWW",
	"MPSADBW",
	"MULB",
	"MULL",
	"MULPD",
	"MULPS",
	"MULQ",
	"MULSD",
	"MULSS",
	"MULW",
	"MULXL",
	"MULXQ",
	"MWAIT",
	"NEGB",
	"NEGL",
	"NEGQ",
	"NEGW",
	"NOPL",
	"NOPW",
	"NOTB",
	"NOTL",
	"NOTQ",
	"NOTW",
	"ORB",
	"ORL",
	"ORPD",
	"ORPS",
	"ORQ",
	"ORW",
	"OUTB",
	"OUTL",
	"OUTSB",
	"OUTSL",
	"OUTSW",
	"OUTW",
	"PABSB",
	"PABSD",
	"PABSW",
	"PACKSSLW",
	"PACKSSWB",
	"PACKUSDW",
	"PACKUSWB",
	"PADDB",
	"PADDL",
	"PADDQ",
	"PADDSB",
	"PADDSW",
	"PADDUSB",
	"PADDUSW",
	"PADDW",
	"PALIGNR",
	"PAND",
	"PANDN",
	"PAUSE",
	"PAVGB",
	"PAVGW",
	"PBLENDVB",
	"PBLENDW",
	"PCLMULQDQ",
	"PCMPEQB",
	"PCMPEQL",
	"PCMPEQQ",
	"PCMPEQW",
	"PCMPESTRI",
	"PCMPESTRM",
	"PCMPGTB",
	"PCMPGTL",
	"PCMPGTQ",
	"PCMPGTW",
	"PCMPISTRI",
	"PCMPISTRM",
	"PDEPL",
	"PDEPQ",
	"PEXTL",
	"PEXTQ",
	"PEXTRB",
	"PEXTRD",
	"PEXTRQ",
	"PEXTRW",
	"PHADDD",
	"PHADDSW",
	"PHADDW",
	"PHMINPOSUW",
	"PHSUBD",
	"PHSUBSW",
	"PHSUBW",
	"PINSRB",
	"PINSRD",
	"PINSRQ",
	"PINSRW",
	"PMADDUBSW",
	"PMADDWL",
	"PMAXSB",
	"PMAXSD",
	"PMAXSW",
	"PMAXUB",
	"PMAXUD",
	"PMAXUW",
	"PMINSB",
	"PMINSD",
	"PMINSW",
	"PMINUB",
	"PMINUD",
	"PMINUW",
	"PMOVMSKB",
	"PMOVSXBD",
	"PMOVSXBQ",
	"PMOVSXBW",
	"PMOVSXDQ",
	"PMOVSXWD",
	"PMOVSXWQ",
	"PMOVZXBD",
	"PMOVZXBQ",
	"PMOVZXBW",
	"PMOVZXDQ",
	"PMOVZXWD",
	"PMOVZXWQ",
	"PMULDQ",
	"PMULHRSW",
	"PMULHUW",
	"PMULHW",
	"PMULLD",
	"PMULLW",
	"PMULULQ",
	"POPAL",
	"POPAW",
	"POPCNTL",
	"POPCNTQ",
	"POPCNTW",
	"POPFL",
	"POPFQ",
	"POPFW",
	"POPL",
	"POPQ",
	"POPW",
	"POR",
	"PREFETCHNTA",
	"PREFETCHT0",
	"PREFETCHT1",
	"PREFETCHT2",
	"PSADBW",
	"PSHUFB",
	"PSHUFD",
	"PSHUFHW",
	"PSHUFL",
	"PSHUFLW",
	"PSHUFW",
	"PSIGNB",
	"PSIGND",
	"PSIGNW",
	"PSLLL",
	"PSLLO",
	"PSLLQ",
	"PSLLW",
	"PSRAL",
	"PSRAW",
	"PSRLL",
	"PSRLO",
	"PSRLQ",
	"PSRLW",
	"PSUBB",
	"PSUBL",
	"PSUBQ",
	"PSUBSB",
	"PSUBSW",
	"PSUBUSB",
	"PSUBUSW",
	"PSUBW",
	"PTEST",
	"PUNPCKHBW",
	"PUNPCKHLQ",
	"PUNPCKHQDQ",
	"PUNPCKHWL",
	"PUNPCKLBW",
	"PUNPCKLLQ",
	"PUNPCKLQDQ",
	"PUNPCKLWL",
	"PUSHAL",
	"PUSHAW",
	"PUSHFL",
	"PUSHFQ",
	"PUSHFW",
	"PUSHL",
	"PUSHQ",
	"PUSHW",
	"PXOR",
	"QUAD",
	"RCLB",
	"RCLL",
	"RCLQ",
	"RCLW",
	"RCPPS",
	"RCPSS",
	"RCRB",
	"RCRL",
	"RCRQ",
	"RCRW",
	"RDFSBASEL",
	"RDFSBASEQ",
	"RDGSBASEL",
	"RDGSBASEQ",
	"RDMSR",
	"RDPKRU",
	"RDPMC",
	"RDRANDL",
	"RDRANDQ",
	"RDRANDW",
	"RDSEEDL",
	"RDSEEDQ",
	"RDSEEDW",
	"RDTSC",
	"RDTSCP",
	"REP",
	"REPN",
	"RETFL",
	"RETFQ",
	"RETFW",
	"ROLB",
	"ROLL",
	"ROLQ",
	"ROLW",
	"RORB",
	"RORL",
	"RORQ",
	"RORW",
	"RORXL",
	"RORXQ",
	"ROUNDPD",
	"ROUNDPS",
	"ROUNDSD",
	"ROUNDSS",
	"RSM",
	"RSQRTPS",
	"RSQRTSS",
	"SAHF",
	"SALB",
	"SALL",
	"SALQ",
	"SALW",
	"SARB",
	"SARL",
	"SARQ",
	"SARW",
	"SARXL",
	"SARXQ",
	"SBBB",
	"SBBL",
	"SBBQ",
	"SBBW",
	"SCASB",
	"SCASL",
	"SCASQ",
	"SCASW",
	"SETCC",
	"SETCS",
	"SETEQ",
	"SETGE",
	"SETGT",
	"SETHI",
	"SETLE",
	"SETLS",
	"SETLT",
	"SETMI",
	"SETNE",
	"SETOC",
	"SETOS",
	"SETPC",
	"SETPL",
	"SETPS",
	"SFENCE",
	"SGDT",
	"SHA1MSG1",
	"SHA1MSG2",
	"SHA1NEXTE",
	"SHA1RNDS4",
	"SHA256MSG1",
	"SHA256MSG2",
	"SHA256RNDS2",
	"SHLB",
	"SHLL",
	"SHLQ",
	"SHLW",
	"SHLXL",
	"SHLXQ",
	"SHRB",
	"SHRL",
	"SHRQ",
	"SHRW",
	"SHRXL",
	"SHRXQ",
	"SHUFPD",
	"SHUFPS",
	"SIDT",
	"SLDTL",
	"SLDTQ",
	"SLDTW",
	"SMSWL",
	"SMSWQ",
	"SMSWW",
	"SQRTPD",
	"SQRTPS",
	"SQRTSD",
	"SQRTSS",
	"STAC",
	"STC",
	"STD",
	"STI",
	"STMXCSR",
	"STOSB",
	"STOSL",
	"STOSQ",
	"STOSW",
	"STRL",
	"STRQ",
	"STRW",
	"SUBB",
	"SUBL",
	"SUBPD",
	"SUBPS",
	"SUBQ",
	"SUBSD",
	"SUBSS",
	"SUBW",
	"SWAPGS",
	"SYSCALL",
	"SYSENTER",
	"SYSENTER64",
	"SYSEXIT",
	"SYSEXIT64",
	"SYSRET",
	"TESTB",
	"TESTL",
	"TESTQ",
	"TESTW",
	"TPAUSE",
	"TZCNTL",
	"TZCNTQ",
	"TZCNTW",
	"UCOMISD",
	"UCOMISS",
	"UD1",
	"UD2",
	"UMWAIT",
	"UNPCKHPD",
	"UNPCKHPS",
	"UNPCKLPD",
	"UNPCKLPS",
	"UMONITOR",
	"V4FMADDPS",
	"V4FMADDSS",
	"V4FNMADDPS",
	"V4FNMADDSS",
	"VADDPD",
	"VADDPS",
	"VADDSD",
	"VADDSS",
	"VADDSUBPD",
	"VADDSUBPS",
	"VAESDEC",
	"VAESDECLAST",
	"VAESENC",
	"VAESENCLAST",
	"VAESIMC",
	"VAESKEYGENASSIST",
	"VALIGND",
	"VALIGNQ",
	"VANDNPD",
	"VANDNPS",
	"VANDPD",
	"VANDPS",
	"VBLENDMPD",
	"VBLENDMPS",
	"VBLENDPD",
	"VBLENDPS",
	"VBLENDVPD",
	"VBLENDVPS",
	"VBROADCASTF128",
	"VBROADCASTF32X2",
	"VBROADCASTF32X4",
	"VBROADCASTF32X8",
	"VBROADCASTF64X2",
	"VBROADCASTF64X4",
	"VBROADCASTI128",
	"VBROADCASTI32X2",
	"VBROADCASTI32X4",
	"VBROADCASTI32X8",
	"VBROADCASTI64X2",
	"VBROADCASTI64X4",
	"VBROADCASTSD",
	"VBROADCASTSS",
	"VCMPPD",
	"VCMPPS",
	"VCMPSD",
	"VCMPSS",
	"VCOMISD",
	"VCOMISS",
	"VCOMPRESSPD",
	"VCOMPRESSPS",
	"VCVTDQ2PD",
	"VCVTDQ2PS",
	"VCVTPD2DQ",
	"VCVTPD2DQX",
	"VCVTPD2DQY",
	"VCVTPD2PS",
	"VCVTPD2PSX",
	"VCVTPD2PSY",
	"VCVTPD2QQ",
	"VCVTPD2UDQ",
	"VCVTPD2UDQX",
	"VCVTPD2UDQY",
	"VCVTPD2UQQ",
	"VCVTPH2PS",
	"VCVTPS2DQ",
	"VCVTPS2PD",
	"VCVTPS2PH",
	"VCVTPS2QQ",
	"VCVTPS2UDQ",
	"VCVTPS2UQQ",
	"VCVTQQ2PD",
	"VCVTQQ2PS",
	"VCVTQQ2PSX",
	"VCVTQQ2PSY",
	"VCVTSD2SI",
	"VCVTSD2SIQ",
	"VCVTSD2SS",
	"VCVTSD2USI",
	"VCVTSD2USIL",
	"VCVTSD2USIQ",
	"VCVTSI2SDL",
	"VCVTSI2SDQ",
	"VCVTSI2SSL",
	"VCVTSI2SSQ",
	"VCVTSS2SD",
	"VCVTSS2SI",
	"VCVTSS2SIQ",
	"VCVTSS2USI",
	"VCVTSS2USIL",
	"VCVTSS2USIQ",
	"VCVTTPD2DQ",
	"VCVTTPD2DQX",
	"VCVTTPD2DQY",
	"VCVTTPD2QQ",
	"VCVTTPD2UDQ",
	"VCVTTPD2UDQX",
	"VCVTTPD2UDQY",
	"VCVTTPD2UQQ",
	"VCVTTPS2DQ",
	"VCVTTPS2QQ",
	"VCVTTPS2UDQ",
	"VCVTTPS2UQQ",
	"VCVTTSD2SI",
	"VCVTTSD2SIQ",
	"VCVTTSD2USI",
	"VCVTTSD2USIL",
	"VCVTTSD2USIQ",
	"VCVTTSS2SI",
	"VCVTTSS2SIQ",
	"VCVTTSS2USI",
	"VCVTTSS2USIL",
	"VCVTTSS2USIQ",
	"VCVTUDQ2PD",
	"VCVTUDQ2PS",
	"VCVTUQQ2PD",
	"VCVTUQQ2PS",
	"VCVTUQQ2PSX",
	"VCVTUQQ2PSY",
	"VCVTUSI2SD",
	"VCVTUSI2SDL",
	"VCVTUSI2SDQ",
	"VCVTUSI2SS",
	"VCVTUSI2SSL",
	"VCVTUSI2SSQ",
	"VDBPSADBW",
	"VDIVPD",
	"VDIVPS",
	"VDIVSD",
	"VDIVSS",
	"VDPPD",
	"VDPPS",
	"VERR",
	"VERW",
	"VEXP2PD",
	"VEXP2PS",
	"VEXPANDPD",
	"VEXPANDPS",
	"VEXTRACTF128",
	"VEXTRACTF32X4",
	"VEXTRACTF32X8",
	"VEXTRACTF64X2",
	"VEXTRACTF64X4",
	"VEXTRACTI128",
	"VEXTRACTI32X4",
	"VEXTRACTI32X8",
	"VEXTRACTI64X2",
	"VEXTRACTI64X4",
	"VEXTRACTPS",
	"VFIXUPIMMPD",
	"VFIXUPIMMPS",
	"VFIXUPIMMSD",
	"VFIXUPIMMSS",
	"VFMADD132PD",
	"VFMADD132PS",
	"VFMADD132SD",
	"VFMADD132SS",
	"VFMADD213PD",
	"VFMADD213PS",
	"VFMADD213SD",
	"VFMADD213SS",
	"VFMADD231PD",
	"VFMADD231PS",
	"VFMADD231SD",
	"VFMADD231SS",
	"VFMADDSUB132PD",
	"VFMADDSUB132PS",
	"VFMADDSUB213PD",
	"VFMADDSUB213PS",
	"VFMADDSUB231PD",
	"VFMADDSUB231PS",
	"VFMSUB132PD",
	"VFMSUB132PS",
	"VFMSUB132SD",
	"VFMSUB132SS",
	"VFMSUB213PD",
	"VFMSUB213PS",
	"VFMSUB213SD",
	"VFMSUB213SS",
	"VFMSUB231PD",
	"VFMSUB231PS",
	"VFMSUB231SD",
	"VFMSUB231SS",
	"VFMSUBADD132PD",
	"VFMSUBADD132PS",
	"VFMSUBADD213PD",
	"VFMSUBADD213PS",
	"VFMSUBADD231PD",
	"VFMSUBADD231PS",
	"VFNMADD132PD",
	"VFNMADD132PS",
	"VFNMADD132SD",
	"VFNMADD132SS",
	"VFNMADD213PD",
	"VFNMADD213PS",
	"VFNMADD213SD",
	"VFNMADD213SS",
	"VFNMADD231PD",
	"VFNMADD231PS",
	"VFNMADD231SD",
	"VFNMADD231SS",
	"VFNMSUB132PD",
	"VFNMSUB132PS",
	"VFNMSUB132SD",
	"VFNMSUB132SS",
	"VFNMSUB213PD",
	"VFNMSUB213PS",
	"VFNMSUB213SD",
	"VFNMSUB213SS",
	"VFNMSUB231PD",
	"VFNMSUB231PS",
	"VFNMSUB231SD",
	"VFNMSUB231SS",
	"VFPCLASSPD",
	"VFPCLASSPDX",
	"VFPCLASSPDY",
	"VFPCLASSPDZ",
	"VFPCLASSPS",
	"VFPCLASSPSX",
	"VFPCLASSPSY",
	"VFPCLASSPSZ",
	"VFPCLASSSD",
	"VFPCLASSSS",
	"VGATHERDPD",
	"VGATHERDPS",
	"VGATHERPF0DPD",
	"VGATHERPF0DPS",
	"VGATHERPF0QPD",
	"VGATHERPF0QPS",
	"VGATHERPF1DPD",
	"VGATHERPF1DPS",
	"VGATHERPF1QPD",
	"VGATHERPF1QPS",
	"VGATHERQPD",
	"VGATHERQPS",
	"VGETEXPPD",
	"VGETEXPPS",
	"VGETEXPSD",
	"VGETEXPSS",
	"VGETMANTPD",
	"VGETMANTPS",
	"VGETMANTSD",
	"VGETMANTSS",
	"VGF2P8AFFINEINVQB",
	"VGF2P8AFFINEQB",
	"VGF2P8MULB",
	"VHADDPD",
	"VHADDPS",
	"VHSUBPD",
	"VHSUBPS",
	"VINSERTF128",
	"VINSERTF32X4",
	"VINSERTF32X8",
	"VINSERTF64X2",
	"VINSERTF64X4",
	"VINSERTI128",
	"VINSERTI32X4",
	"VINSERTI32X8",
	"VINSERTI64X2",
	"VINSERTI64X4",
	"VINSERTPS",
	"VLDDQU",
	"VLDMXCSR",
	"VMASKMOVDQU",
	"VMASKMOVPD",
	"VMASKMOVPS",
	"VMAXPD",
	"VMAXPS",
	"VMAXSD",
	"VMAXSS",
	"VMINPD",
	"VMINPS",
	"VMINSD",
	"VMINSS",
	"VMOVAPD",
	"VMOVAPS",
	"VMOVD",
	"VMOVDDUP",
	"VMOVDQA",
	"VMOVDQA32",
	"VMOVDQA64",
	"VMOVDQU",
	"VMOVDQU16",
	"VMOVDQU32",
	"VMOVDQU64",
	"VMOVDQU8",
	"VMOVHLPS",
	"VMOVHPD",
	"VMOVHPS",
	"VMOVLHPS",
	"VMOVLPD",
	"VMOVLPS",
	"VMOVMSKPD",
	"VMOVMSKPS",
	"VMOVNTDQ",
	"VMOVNTDQA",
	"VMOVNTPD",
	"VMOVNTPS",
	"VMOVQ",
	"VMOVSD",
	"VMOVSHDUP",
	"VMOVSLDUP",
	"VMOVSS",
	"VMOVUPD",
	"VMOVUPS",
	"VMPSADBW",
	"VMULPD",
	"VMULPS",
	"VMULSD",
	"VMULSS",
	"VORPD",
	"VORPS",
	"VP4DPWSSD",
	"VP4DPWSSDS",
	"VPABSB",
	"VPABSD",
	"VPABSQ",
	"VPABSW",
	"VPACKSSDW",
	"VPACKSSWB",
	"VPACKUSDW",
	"VPACKUSWB",
	"VPADDB",
	"VPADDD",
	"VPADDQ",
	"VPADDSB",
	"VPADDSW",
	"VPADDUSB",
	"VPADDUSW",
	"VPADDW",
	"VPALIGNR",
	"VPAND",
	"VPANDD",
	"VPANDN",
	"VPANDND",
	"VPANDNQ",
	"VPANDQ",
	"VPAVGB",
	"VPAVGW",
	"VPBLENDD",
	"VPBLENDMB",
	"VPBLENDMD",
	"VPBLENDMQ",
	"VPBLENDMW",
	"VPBLENDVB",
	"VPBLENDW",
	"VPBROADCASTB",
	"VPBROADCASTD",
	"VPBROADCASTMB2Q",
	"VPBROADCASTMW2D",
	"VPBROADCASTQ",
	"VPBROADCASTW",
	"VPCLMULQDQ",
	"VPCMPB",
	"VPCMPD",
	"VPCMPEQB",
	"VPCMPEQD",
	"VPCMPEQQ",
	"VPCMPEQW",
	"VPCMPESTRI",
	"VPCMPESTRM",
	"VPCMPGTB",
	"VPCMPGTD",
	"VPCMPGTQ",
	"VPCMPGTW",
	"VPCMPISTRI",
	"VPCMPISTRM",
	"VPCMPQ",
	"VPCMPUB",
	"VPCMPUD",
	"VPCMPUQ",
	"VPCMPUW",
	"VPCMPW",
	"VPCOMPRESSB",
	"VPCOMPRESSD",
	"VPCOMPRESSQ",
	"VPCOMPRESSW",
	"VPCONFLICTD",
	"VPCONFLICTQ",
	"VPDPBUSD",
	"VPDPBUSDS",
	"VPDPWSSD",
	"VPDPWSSDS",
	"VPERM2F128",
	"VPERM2I128",
	"VPERMB",
	"VPERMD",
	"VPERMI2B",
	"VPERMI2D",
	"VPERMI2PD",
	"VPERMI2PS",
	"VPERMI2Q",
	"VPERMI2W",
	"VPERMILPD",
	"VPERMILPS",
	"VPERMPD",
	"VPERMPS",
	"VPERMQ",
	"VPERMT2B",
	"VPERMT2D",
	"VPERMT2PD",
	"VPERMT2PS",
	"VPERMT2Q",
	"VPERMT2W",
	"VPERMW",
	"VPEXPANDB",
	"VPEXPANDD",
	"VPEXPANDQ",
	"VPEXPANDW",
	"VPEXTRB",
	"VPEXTRD",
	"VPEXTRQ",
	"VPEXTRW",
	"VPGATHERDD",
	"VPGATHERDQ",
	"VPGATHERQD",
	"VPGATHERQQ",
	"VPHADDD",
	"VPHADDSW",
	"VPHADDW",
	"VPHMINPOSUW",
	"VPHSUBD",
	"VPHSUBSW",
	"VPHSUBW",
	"VPINSRB",
	"VPINSRD",
	"VPINSRQ",
	"VPINSRW",
	"VPLZCNTD",
	"VPLZCNTQ",
	"VPMADD52HUQ",
	"VPMADD52LUQ",
	"VPMADDUBSW",
	"VPMADDWD",
	"VPMASKMOVD",
	"VPMASKMOVQ",
	"VPMAXSB",
	"VPMAXSD",
	"VPMAXSQ",
	"VPMAXSW",
	"VPMAXUB",
	"VPMAXUD",
	"VPMAXUQ",
	"VPMAXUW",
	"VPMINSB",
	"VPMINSD",
	"VPMINSQ",
	"VPMINSW",
	"VPMINUB",
	"VPMINUD",
	"VPMINUQ",
	"VPMINUW",
	"VPMOVB2M",
	"VPMOVD2M",
	"VPMOVDB",
	"VPMOVDW",
	"VPMOVM2B",
	"VPMOVM2D",
	"VPMOVM2Q",
	"VPMOVM2W",
	"VPMOVMSKB",
	"VPMOVQ2M",
	"VPMOVQB",
	"VPMOVQD",
	"VPMOVQW",
	"VPMOVSDB",
	"VPMOVSDW",
	"VPMOVSQB",
	"VPMOVSQD",
	"VPMOVSQW",
	"VPMOVSWB",
	"VPMOVSXBD",
	"VPMOVSXBQ",
	"VPMOVSXBW",
	"VPMOVSXDQ",
	"VPMOVSXWD",
	"VPMOVSXWQ",
	"VPMOVUSDB",
	"VPMOVUSDW",
	"VPMOVUSQB",
	"VPMOVUSQD",
	"VPMOVUSQW",
	"VPMOVUSWB",
	"VPMOVW2M",
	"VPMOVWB",
	"VPMOVZXBD",
	"VPMOVZXBQ",
	"VPMOVZXBW",
	"VPMOVZXDQ",
	"VPMOVZXWD",
	"VPMOVZXWQ",
	"VPMULDQ",
	"VPMULHRSW",
	"VPMULHUW",
	"VPMULHW",
	"VPMULLD",
	"VPMULLQ",
	"VPMULLW",
	"VPMULTISHIFTQB",
	"VPMULUDQ",
	"VPOPCNTB",
	"VPOPCNTD",
	"VPOPCNTQ",
	"VPOPCNTW",
	"VPOR",
	"VPORD",
	"VPORQ",
	"VPROLD",
	"VPROLQ",
	"VPROLVD",
	"VPROLVQ",
	"VPRORD",
	"VPRORQ",
	"VPRORVD",
	"VPRORVQ",
	"VPSADBW",
	"VPSCATTERDD",
	"VPSCATTERDQ",
	"VPSCATTERQD",
	"VPSCATTERQQ",
	"VPSHLDD",
	"VPSHLDQ",
	"VPSHLDVD",
	"VPSHLDVQ",
	"VPSHLDVW",
	"VPSHLDW",
	"VPSHRDD",
	"VPSHRDQ",
	"VPSHRDVD",
	"VPSHRDVQ",
	"VPSHRDVW",
	"VPSHRDW",
	"VPSHUFB",
	"VPSHUFBITQMB",
	"VPSHUFD",
	"VPSHUFHW",
	"VPSHUFLW",
	"VPSIGNB",
	"VPSIGND",
	"VPSIGNW",
	"VPSLLD",
	"VPSLLDQ",
	"VPSLLQ",
	"VPSLLVD",
	"VPSLLVQ",
	"VPSLLVW",
	"VPSLLW",
	"VPSRAD",
	"VPSRAQ",
	"VPSRAVD",
	"VPSRAVQ",
	"VPSRAVW",
	"VPSRAW",
	"VPSRLD",
	"VPSRLDQ",
	"VPSRLQ",
	"VPSRLVD",
	"VPSRLVQ",
	"VPSRLVW",
	"VPSRLW",
	"VPSUBB",
	"VPSUBD",
	"VPSUBQ",
	"VPSUBSB",
	"VPSUBSW",
	"VPSUBUSB",
	"VPSUBUSW",
	"VPSUBW",
	"VPTERNLOGD",
	"VPTERNLOGQ",
	"VPTEST",
	"VPTESTMB",
	"VPTESTMD",
	"VPTESTMQ",
	"VPTESTMW",
	"VPTESTNMB",
	"VPTESTNMD",
	"VPTESTNMQ",
	"VPTESTNMW",
	"VPUNPCKHBW",
	"VPUNPCKHDQ",
	"VPUNPCKHQDQ",
	"VPUNPCKHWD",
	"VPUNPCKLBW",
	"VPUNPCKLDQ",
	"VPUNPCKLQDQ",
	"VPUNPCKLWD",
	"VPXOR",
	"VPXORD",
	"VPXORQ",
	"VRANGEPD",
	"VRANGEPS",
	"VRANGESD",
	"VRANGESS",
	"VRCP14PD",
	"VRCP14PS",
	"VRCP14SD",
	"VRCP14SS",
	"VRCP28PD",
	"VRCP28PS",
	"VRCP28SD",
	"VRCP28SS",
	"VRCPPS",
	"VRCPSS",
	"VREDUCEPD",
	"VREDUCEPS",
	"VREDUCESD",
	"VREDUCESS",
	"VRNDSCALEPD",
	"VRNDSCALEPS",
	"VRNDSCALESD",
	"VRNDSCALESS",
	"VROUNDPD",
	"VROUNDPS",
	"VROUNDSD",
	"VROUNDSS",
	"VRSQRT14PD",
	"VRSQRT14PS",
	"VRSQRT14SD",
	"VRSQRT14SS",
	"VRSQRT28PD",
	"VRSQRT28PS",
	"VRSQRT28SD",
	"VRSQRT28SS",
	"VRSQRTPS",
	"VRSQRTSS",
	"VSCALEFPD",
	"VSCALEFPS",
	"VSCALEFSD",
	"VSCALEFSS",
	"VSCATTERDPD",
	"VSCATTERDPS",
	"VSCATTERPF0DPD",
	"VSCATTERPF0DPS",
	"VSCATTERPF0QPD",
	"VSCATTERPF0QPS",
	"VSCATTERPF1DPD",
	"VSCATTERPF1DPS",
	"VSCATTERPF1QPD",
	"VSCATTERPF1QPS",
	"VSCATTERQPD",
	"VSCATTERQPS",
	"VSHUFF32X4",
	"VSHUFF64X2",
	"VSHUFI32X4",
	"VSHUFI64X2",
	"VSHUFPD",
	"VSHUFPS",
	"VSQRTPD",
	"VSQRTPS",
	"VSQRTSD",
	"VSQRTSS",
	"VSTMXCSR",
	"VSUBPD",
	"VSUBPS",
	"VSUBSD",
	"VSUBSS",
	"VTESTPD",
	"VTESTPS",
	"VUCOMISD",
	"VUCOMISS",
	"VUNPCKHPD",
	"VUNPCKHPS",
	"VUNPCKLPD",
	"VUNPCKLPS",
	"VXORPD",
	"VXORPS",
	"VZEROALL",
	"VZEROUPPER",
	"WAIT",
	"WBINVD",
	"WORD",
	"WRFSBASEL",
	"WRFSBASEQ",
	"WRGSBASEL",
	"WRGSBASEQ",
	"WRMSR",
	"WRPKRU",
	"XABORT",
	"XACQUIRE",
	"XADDB",
	"XADDL",
	"XADDQ",
	"XADDW",
	"XBEGIN",
	"XCHGB",
	"XCHGL",
	"XCHGQ",
	"XCHGW",
	"XEND",
	"XGETBV",
	"XLAT",
	"XORB",
	"XORL",
	"XORPD",
	"XORPS",
	"XORQ",
	"XORW",
	"XRELEASE",
	"XRSTOR",
	"XRSTOR64",
	"XRSTORS",
	"XRSTORS64",
	"XSAVE",
	"XSAVE64",
	"XSAVEC",
	"XSAVEC64",
	"XSAVEOPT",
	"XSAVEOPT64",
	"XSAVES",
	"XSAVES64",
	"XSETBV",
	"XTEST",
	"LAST",
}
