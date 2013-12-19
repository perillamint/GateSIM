/* C Implementation of GateCode -- 2003 November 6 */
// Copyright 2003 T.Pittman
// ** This is not beautiful code, but it does seem to work **

/* see: InitMacros (below) for the built-in macros */

#define GateObjFi FILE
#define OutBuffSize 10000
#define MaxStrs 2000000
#define MaxSyms 500000
#define MaxNet 500000
#define HashSize 14
#define AllMacros 1

#include "Gates.h"
// -------------------------------------------------

int DEBUGGING = 0;
int RunDebug = 0;

int MemSize, NetSize, TraceSize;
int Cycle, ClockRate, PonDelay, Trate, TraPh, NextClock, RunTo, Glitch;
int MemAt, DataAt, NetAt, TraceAt, TraceGate;
int UndefinedMem = -1;
int ROMchip = 0;
int RAMchip = 0;
int doClox = 0;
int MemList = 0;
int newHeads = 0;
int ErrCount = 0;
int StringOflo = 0;
int WdOffs;

int *Memory = NULL;
int *NetList = NULL;
int *TraceList = NULL;
byte *NetInvert = NULL;

MidString Headers;
char OutData[OutBuffSize];		/* output panel shadow text */

#define HashLink 0
#define SymOffs 1
#define NetDefn 2
#define GateNo 3
HugeString StringTable;
int Symbols[MaxSyms];
int HashTable[1 << HashSize];
char Caps[256];
int NetIndex[MaxNet + 99];
int NextNetx;
int NextStr;
int NextSym;
int RenumMacro;

FILE *TheLogFile = NULL;

/* safe string operators, because C is not safe... */

SmallString zWord;
void StrZap(char *theStr)
{
	*theStr = '\0';
}

void StrReplace(char *theStr, char oldc, char newc)
{								/* 1-char replace */
	int ix = strlen(theStr);
	while (--ix >= 0)
		if (theStr[ix] == oldc)
			theStr[ix] = newc;
}

int StrOffs(char *theStr, char *aStr)
{								/* returns offset, or -1 if not there */
	char *here = strstr(theStr, aStr);	/* returns pointer to aStr in theStr */
	if (here < theStr || here > &theStr[strlen(theStr)])
		return -1;
	return here - theStr;
}

void StrCpyCk(int mx, char *deStr, char *theStr)
{								/* copies up to mx chars */
	while ((--mx >= 0) && (*theStr != '\0'))
		*deStr++ = *theStr++;
	StrZap(deStr);
}

void StrCatCk(int mx, char *deStr, char *theStr)
{								/* like strcat, but safe */
	int nx = strlen(deStr);
	int nz = strlen(theStr);
	if (nx + nz >= mx)
		StringOflo++;			/* report lost data, if so */
	else
		StrCpyCk(nz, &deStr[nx], theStr);
}

void SubStrCpy(char *deStr, char *theStr, int fst, int lst)
{								/* extract substring */
	char *here = deStr;
	if (deStr == theStr && fst == 0)
		here += lst;
	else
		while (fst < lst)
		{
			if ((*here++ = theStr[fst++]) == '\0')
				break;
		}
	StrZap(here);
}

char *SubStr(char *theStr, int fst, int lst)
{								/* functional version of SubStrCpy */
	SubStrCpy(zWord.s, theStr, fst, lst);
	return zWord.s;
}

char *Num2Str(char *theStr, int valu)
{								/* returns string version of int>0 */
	if (valu > 9)
		theStr = Num2Str(theStr, valu / 10);
	*theStr++ = (char)(valu % 10 + 48);
	return theStr;
}

char *StrOf(int valu)
{								/* a more general version of Num2Str */
	char *theStr;
	theStr = zWord.s;
	if (valu < 0)
	{
		*theStr++ = '-';
		valu = -valu;
	}
	theStr = Num2Str(theStr, valu);
	StrZap(theStr);
	return zWord.s;
}

/* other utilities... */

int IntOf(char *theStr)
{								/* convert string to integer */
	int theNum, ix;
	char ch;
	theNum = 0;
	for (ix = 0; ix < (int)strlen(theStr); ix++)
	{
		ch = theStr[ix];
		if (ch == ' ')
			continue;
		if (ch < '0')
			return -1;
		if (ch > '9')
			return -1;
		theNum = theNum * 10 + ch % 16;
	}
	return theNum;
}								/* IntOf */

SmallString SavedStr;
int FindsInt;					/* the last suffix number seen */
char *SpellSym(int sym)
{
	return &StringTable.s[Symbols[sym + SymOffs]];
}

int FindSym(char *theStr)
{								/* find (possibly insert) theStr in symbol
								   table */
	int ix, hash, here, thar, neq;
	int len = strlen(theStr);
	char *astr = theStr;
	char ch = *astr;
	neq = 2;
	if (len == 1)
		if (FindsInt >= 0)
		{						/* replicate symbol sequences.. */
			if (ch == '~')
				neq = 0;
			else if (ch == '+')
				neq = 1;
			else if (ch == '-')
				neq = -1;
			if (neq < 2)
			{
				StrCatCk(99, SavedStr.s, StrOf(FindsInt + neq));
				astr = &SavedStr.s[0];
				len = strlen(SavedStr.s);
			}
		}
	if (len + NextStr >= MaxStrs)
	{
		StringOflo++;
		return 0;
	}
	FindsInt = -1;
	hash = 0;
	here = 0;
	for (ix = 0; *astr != '\0'; ix++)
	{
		ch = *astr++;
		hash = ((hash >> (HashSize - 3)) & 7) + (hash << 3) + Caps[ch];
		StringTable.s[ix + NextStr] = ch;
		if (ix < 99)
			SavedStr.s[ix] = ch;
		if (ch == '.')
		{						/* update the suffix number.. */
			here = ix;
			FindsInt = 0;
		}
		else if (ch < '0')
			FindsInt = -1;
		else if (ch > '9')
			FindsInt = -1;
		else if (FindsInt >= 0)
			FindsInt = FindsInt * 10 - 48 + (int)ch;
	}
	if (here < 99)
		SavedStr.s[here + 1] = '\0';
	else
		FindsInt = -1;
	hash = hash & ((1 << HashSize) - 1);
	here = HashTable[hash];
	ix = 0;
	while (here > 0)
	{							/* on exit, ix is final here>0 */
		thar = Symbols[here + SymOffs];
		neq = 0;
		if (StringTable.s[len + thar] != '\0')
			neq = 1;
		else
			for (ix = 0; ix < len; ix++)
				if (Caps[StringTable.s[ix + NextStr]]
					!= Caps[StringTable.s[ix + thar]])
				{
					neq = 1;
					break;
				}
		if (neq == 0)
			return here;
		ix = here;
		here = Symbols[here + HashLink];
	}
	if (NextSym >= MaxSyms)
	{
		StringOflo++;
		return 0;
	}
	if (ix > 0)
		Symbols[ix + HashLink] = NextSym;
	else
		HashTable[hash] = NextSym;
	here = NextSym;
	Symbols[here + HashLink] = 0;
	Symbols[here + SymOffs] = NextStr;
	Symbols[here + NetDefn] = 0;
	Symbols[here + GateNo] = 0;
	NextSym = here + 4;
	NextStr = NextStr + len;
	StringTable.s[NextStr++] = '\0';
	return here;
}								/* end FindSym */

int EveryUpBy, theCount, theLimit;
void Pacify(int doWhat, char *theMsg)
{								/* for large files on slow hardware.. */
	if (doWhat < 0)
		theLimit = 0;
	theCount = theCount + 1;
	if (doWhat > 0)
	{
		EveryUpBy = doWhat;
		theLimit = doWhat;
		theCount = 0;
	}
	else if (theCount >= theLimit)
	{
		LogIt(StrOf(theCount));
		LogMo(theMsg);
		LogOut();
		theLimit = theLimit + EveryUpBy;
		if (theLimit == EveryUpBy * 10)
			EveryUpBy = theLimit;
	}
}								/* end Pacify */

void LogMo(char *theMsg)
{								/* this is used in debug mode for logging.. */
	int bksz = sizeof(OutData) / 2;
	int len = strlen(theMsg);
	if (strlen(OutData) + len < sizeof(OutData))
		StrCatCk(sizeof(OutData), OutData, theMsg);
	else
		while (len > 0)
		{
			LogOut();
			StrCpyCk(bksz, OutData, theMsg);
			theMsg += bksz;
			len = len - bksz;
		}
}								/* end LogMo */

void LogNum(int theNum)
{
	LogMo(StrOf(theNum));
}								/* end LogNum */

void LogIt(char *theMsg)
{
	LogMo("\r\n");
	LogMo(theMsg);
}								/* end LogIt */

void ReadData(GateObjFi * theObj, char *InData, int DataLen)
{
	FILE *altFile;
	int ix;
	char *aStr;
	SmallString aWord;
	MidString aLine;
	TheLogFile = theObj;
	StrZap(OutData);
	LogOut();
	for (ix = 0; ix < (1 << HashSize); ix++)
		HashTable[ix] = 0;
	for (ix = 0; ix < 256; ix++)
		Caps[ix] = (char)ix;
	for (ix = 0; ix < 26; ix++)
		Caps[ix + (int)'A'] = Caps[ix + (int)'a'];
	FindsInt = -1;
	aStr = strstr(InData, "[0x00400000]");
	if (aStr)
	{							/* got MIPS dump.. */
		StrCpyCk(99, StringTable.s, "\r\rROM DATA");
		aStr = aStr - 48;
		aStr = strstr(aStr, "Text Segment");
		StrZap(aLine.s);
		LogIt("; ROM DATA at 0x00400000..");
		aStr = strstr(aStr, "[0x0040");
		while (aStr)
		{						/* the real one */
			if (strlen(aLine.s) == 0)
			{
				SubStrCpy(aWord.s, aStr, 7, 11);
				ix = Numify(aWord.s, 16) / 4;
				StrCpyCk(99, aWord.s, StrOf(ix));
				StrCatCk(99, aWord.s, " DATA");
				StrCpyCk(99, aLine.s, aWord.s);
				if (ix > 0)
					StrCatCk(99999, StringTable.s, aWord.s);
			}
			SubStrCpy(aWord.s, aStr, 18, 30);
			StrCatCk(999, aLine.s, aWord.s);
			StrCatCk(99999, StringTable.s, aWord.s);
			if (strlen(aLine.s) > 50)
			{
				LogIt(aLine.s);
				LogOut();
				StrZap(aLine.s);
				StrCatCk(99999, StringTable.s, "\r");
			}
			aStr = strstr(aStr + 32, "[0x0040");
		}
		if (strlen(aLine.s) > 0)
		{
			LogIt(aLine.s);
			LogOut();
		}
		aStr = strstr(InData, "Data Segment");
		LogIt("; RAM DATA at 0x10010000..");
		aStr = strstr(aStr, "[0x10010000]");
		while (aStr)
		{
			SubStrCpy(aLine.s, aStr, 7, 88);
			aStr = strstr(aStr + 32, "[0x1001");
			if (strstr(aLine.s, "..."))
				continue;
			SubStrCpy(aWord.s, aLine.s, 0, 4);
			ix = Numify(aWord.s, 16) / 4;
			StrCpyCk(99, aWord.s, StrOf(ix));
			StrCatCk(99, aWord.s, " DATA ");
			if (ix > 0)
				StrCatCk(99999, StringTable.s, aWord.s);
			else
				StrCatCk(99999, StringTable.s, "\rRAM DATA ");
			LogIt(aWord.s);
			for (ix = 2; ix <= 5; ix++)
			{
				StrCpyCk(99, aWord.s, GetWord(ix, aLine.s));
				StrCatCk(99, aWord.s, " ");
				LogMo(aWord.s);
				StrCatCk(99999, StringTable.s, aWord.s);
			}
			LogOut();
			StrCatCk(99999, StringTable.s, "\r");
		}
		if (DefaultFile)
		{
			InData = NULL;
			altFile = fopen(DefaultFile, "rb");
			if (altFile)
				if (fseek(altFile, 0, SEEK_END) == 0)
					if ((ix = ftell(altFile)) > 0)
						if (fseek(altFile, 0, SEEK_SET) == 0)
						{
							NextStr = strlen(StringTable.s) + ix + 99;
							InData = (char *)malloc(NextStr);
						}
			if (InData == NULL)
				return;
			for (ix = 0; !feof(altFile); ix++)
				InData[ix] = (char)getc(altFile);
			InData[ix] = '\0';
			fclose(altFile);
			StrCatCk(NextStr, InData, StringTable.s);
			DataLen = strlen(InData);
			if (StringOflo)
			{
				SayError("Memory data overflow: ");
				LogNum(DataLen);
				LogMo("/");
				LogNum(NextStr);
				LogOut();
			}
		}
		else
			return;
	}							/* end if (MIPS) */
	StrZap(StringTable.s);
	NextStr = 0;
	NextSym = 0;
	NextNetx = 0;
	NetIndex[NextNetx++] = -1;
	// CheckOflo(DataLen, 100000, "InData");
	if (FindSym("") != 0)
		SayError("Oops=0");
	if (FindSym("GATE") != 4)
		SayError("Oops=1");
	if (FindSym("HEX") != 8)
		SayError("Oops=2");
	if (FindSym("CHIP") != 12)
		SayError("Oops=3");
	if (FindSym("ROM") != 16)
		SayError("Oops=4");
	if (FindSym("RAM") != 20)
		SayError("Oops=5");
	if (FindSym("DATA") != 24)
		SayError("Oops=6");
	if (FindSym("=") != 28)
		SayError("Oops=7");
	if (FindSym("0") != 32)
		SayError("Oops=8");
	Symbols[32 + GateNo] = 0;
	if (FindSym("1") != 36)
		SayError("Oops=9");
	Symbols[36 + GateNo] = 1;
	if (FindSym("CLK/") != 40)
		SayError("Oops=10");
	Symbols[40 + GateNo] = 2;
	if (FindSym("CLK") != 44)
		SayError("Oops=11");
	Symbols[44 + GateNo] = 4;
	if (FindSym("RESET") != 48)
		SayError("Oops=12");
	Symbols[48 + GateNo] = 6;
	if (FindSym("TRACED") != 52)
		SayError("Oops=13");
	Symbols[52 + GateNo] = 8;
	if (FindSym("X") != 56)
		SayError("Oops=14");
	Symbols[56 + GateNo] = 10;
	if (FindSym("END") != 60)
		SayError("Oops=15");
	if (FindSym("+DB+") != 64)
		SayError("Oops=16");
	TraceGate = 0;
	StrZap(Headers.s);
	MemSize = 2;
	NetSize = NetStart;
	TraceSize = 0;
	doClox = 0;
	ClockRate = 0;
	PonDelay = 0;
	Trate = 0;
	TraPh = 0;
	Pacify(1000, "");
	InitMacros();
	if (DEBUGGING > 1)
	{
		LogIt("NextNetx=");
		LogNum(NextNetx);
		LogMo(", NetSize=");
		LogNum(NetSize);
		LogMo(", MemSize=");
		LogNum(MemSize);
		LogMo(", TraceSize=");
		LogNum(TraceSize);
		LogMo(", DataLen=");
		LogNum(DataLen);
		LogIt("");
		LogOut();
	}
	Pacify(10000, "");
	DataIn(InData, DataLen);
	if (DEBUGGING > 0)
	{
		LogIt("");
		LogIt("");
		LogNum(NextNetx);
		LogMo("# NetSize=");
		LogNum(NetSize);
		LogMo(", MemSize=");
		LogNum(MemSize);
		LogMo(", TraceSize=");
		LogNum(TraceSize);
		LogIt("");
		LogIt("");
		LogOut();
	}
	Pacify(-1, " source lines total");
	/* InData = null; -- (done with this) OK, now build data structures.. */
	Memory = (int *)malloc((++MemSize) * sizeof(int));
	if (DEBUGGING > 2)
	{
		LogIt("* Memory=");
		LogNum(MemSize);
		LogOut();
	}
	TraceList = (int *)malloc((++TraceSize) * sizeof(int));
	if (DEBUGGING > 2)
	{
		LogIt("* TraceList=");
		LogNum(TraceSize);
		LogOut();
	}
	NetList = (int *)malloc((++NetSize) * sizeof(int));
	NetInvert = (byte *) malloc(NetSize * sizeof(byte));
	if (DEBUGGING > 2)
	{
		LogIt("* NetList=");
		LogNum(NetSize);
		LogOut();
	}
	for (ix = 0; ix < NetSize; ix++)
	{
		NetList[ix] = 0;
		NetInvert[ix] = 0;
	}
	NetSize = NetSize - 1;		/* back to actual.. */
	MemSize = MemSize - 1;
	TraceSize = TraceSize - 1;
	NetInvert[0] = 32;
	NetList[0] = 0;
	NetInvert[1] = 36;
	NetList[1] = 1;
	NetAt = NetBase;
	NetInvert[NetAt] = 40;
	NetList[NetAt++] = 2;		/* CLK/ [3] */
	NetList[NetAt++] = 0;
	NetInvert[NetAt] = 44;
	NetList[NetAt++] = 2;		/* CLK [5] */
	NetList[NetAt++] = 0;
	NetInvert[NetAt] = 48;
	NetList[NetAt++] = 2;		/* RESET [7] */
	NetList[NetAt++] = 0;
	NetInvert[NetAt] = 52;
	NetList[NetAt++] = 2;		/* TRACED [9] */
	NetList[NetAt++] = 0;
	NetInvert[NetAt] = 56;
	NetList[NetAt++] = 2;		/* x [11] */
	NetList[NetAt++] = -1;
	if (NetAt != NetStart)
		SayError("Oops/NetStart");
	Memory[0] = 0;
	Memory[1] = 0;
	Memory[2] = 0;
	MemAt = 1;
	DataAt = MemSize;
	TraceAt = 0;
	if (Trate < 0)
		Trate = -Symbols[TraceGate + GateNo];
	else if (Trate == 0)
		Trate = 1;
	BuildNet();
	LogIt("Str=");
	LogNum(NextStr / 10000);
	LogMo("/");
	LogNum(MaxStrs / 10000);
	LogMo(", Sym=");
	LogNum(NextSym / 10000);
	LogMo("/");
	LogNum(MaxSyms / 10000);
	LogMo(", Net=");
	LogNum(NextNetx / 10000);
	LogMo("/");
	LogNum(MaxNet / 10000);
	LogIt("");
	LogOut();
	if (DEBUGGING > 0)
	{
		LogIt("");
		LogIt("NetSize=");
		LogNum(NetAt);
		LogMo(", MemAt=");
		LogNum(MemAt);
		LogMo("/");
		LogNum(DataAt);
		LogMo(", TraceAt=");
		LogNum(TraceAt);
		LogIt("");
		LogOut();
	}
	if (NetSize < NetAt || DataAt < MemAt || TraceSize < TraceAt)
		SayError("Table Overflow ***");
	CheckOflo(NextStr, MaxStrs, "StringTable");
	CheckOflo(NextSym, MaxSyms, "SymbolTable");
	Memory[0] = MemAt;
	Memory[MemAt] = 0;
	NetList[NetAt] = 0;
	TraceSize = TraceAt;
	StrCatCk(999, Headers.s, " #");
	LogIt(Headers.s);
	LogOut();
	Cycle = 0;
	NetList[3] = 1;
	NetList[5] = 0;
	NetList[7] = 0;
	NetList[9] = 1;
	NetList[11] = -1;
	Glitch = 0;
	doClox = -doClox;
	if (doClox <= 0)
		doClox = 1;
	NextClock = 0;
	if (DEBUGGING > 0)
	{
		if (DEBUGGING > 1)
		{
			StrCpyCk(999, aLine.s, "TraceList=");
			for (ix = 0; ix < TraceAt; ix++)
			{
				if ((ix & 31) == 0)
				{
					LogIt(aLine.s);
					StrZap(aLine.s);
				}
				StrCatCk(999, aLine.s, " ");
				StrCatCk(999, aLine.s, StrOf(TraceList[ix]));
			}
			LogIt("");
			LogIt(aLine.s);
			LogIt("");
		}
		DumpAll();
	}
	if (ErrCount > 0)
	{
		StrCpyCk(999, aLine.s, "Aborting, due to ");
		StrCatCk(999, aLine.s, StrOf(ErrCount));
		StrCatCk(999, aLine.s, " errors");
		SayError(aLine.s);
		LogOut();
		exit(1);
	}
}								/* end ReadData */

void DataIn(char *InData, int DataLen)
{
	/* copy InData to NetIndex[NextNetx++] and build symbol table; */
	/* this is used both for built-in macros, and for user data.. */
	int ix, xi, lino, here, wcnt, nbits, theName, theType, front, MemTail;
	int inChip, inMem, thar, StarNo;
	char ch;
	SmallString aWord, xWord;
	MidString Listing, aLine, zLine, StarLn;
	StrZap(StarLn.s);
	StrZap(Listing.s);
	inChip = 0;
	inMem = 0;
	nbits = 0;
	lino = 0;
	StarNo = -1;
	if (DEBUGGING > 0)
	{
		LogIt("DataLen=");
		LogNum(DataLen);
		LogOut();
	}
	MemTail = MemList;			/* initially =0, so loop in next line is not
								   executed */
	if (MemTail > 0)
		while (NetIndex[MemTail + 2] > 0)
			MemTail = NetIndex[MemTail + 2];
	while (lino < DataLen)
	{
		if (StringOflo)
		{
			SayError("Some data was lost: ");
			LogMo(Listing.s);
			CheckOflo(NextStr, MaxStrs, "StringTable");
			CheckOflo(NextSym, MaxSyms, "SymbolTable");
			CheckOflo(NextNetx, MaxNet, "NetIndex");
			LogIt("");
			LogOut();
			exit(1);
		}
		if (InData[lino] < ' ')
		{						/* get to front of next line.. */
			lino++;
			continue;
		}
		thar = 0;
		here = lino;
		wcnt = -1;
		front = 0;
		while (lino < DataLen)
		{						/* get to its end, while looking for semi/star 
								 */
			ch = InData[lino];
			if (thar > 0)
			{
				if (ch < ' ')
				{
					InData[lino] = ' ';
					ch = ' ';
				}
				else
					thar = 0;
			}
			if (ch < ' ')
				break;
			if (wcnt < 0)
			{
				if (ch == ';')
					wcnt = lino;
				else if (ch == '\\')
				{
					InData[lino] = ' ';
					thar++;
				}
				else if (front == 0)
					if (ch == '*')
						front = lino;
			}
			lino++;
		}
		SubStrCpy(zLine.s, InData, here, lino);
		if (wcnt < 0)
			wcnt = lino;
		SubStrCpy(aLine.s, zLine.s, 0, wcnt - here);
		if (front > 0)
		{						/* got a star on this line... */
			if (InData[front - 1] != ' ')
			{
				StrCpyCk(999, Listing.s, zLine.s);
				StrCpyCk(999, StarLn.s, aLine.s);
				if (DEBUGGING > 1)
				{
					LogIt(StarLn.s);
					LogOut();
				}
				continue;
			}
			else if (strlen(StarLn.s) > 0)
			{					/* dupe previous StarLn with StarNo for * */
				if (StarNo < 0)
					StarNo = IntOf(GetWord(1, aLine.s));
				xi = 0;
				if (StarNo >= 0)
					for (ix = 0;; ix++)
					{
						if (StarLn.s[ix] < ' ')
							break;
						if (StarLn.s[ix] == '*')
						{
							aLine.s[xi] = '\0';
							StrCatCk(999, aLine.s, StrOf(StarNo));
							xi = strlen(aLine.s);
						}
						else
							aLine.s[xi++] = StarLn.s[ix];
					}
				aLine.s[xi] = '\0';
				StarNo = StarNo - 1;
				if (StarNo >= 0)
					lino = here;	/* repeat this line every time but the
									   last */
				else
					StrZap(StarLn.s);
			}
			else
				StrZap(aLine.s);
		}
		else
			StrCpyCk(999, Listing.s, zLine.s);
		Pacify(0, " source lines read");
		StrReplace(aLine.s, ',', ' '); /* ignore blanks */
		ix = StrOffs(aLine.s, "=");
		if (ix > 0)
			if (StrOffs(aLine.s, " = ") < 0)
			{					/* insert blanks around '=' .. */
				SubStrCpy(zLine.s, aLine.s, ix + 1, ix + 999);
				SubStrCpy(aLine.s, aLine.s, 0, ix);
				StrCatCk(999, aLine.s, " = ");
				StrCatCk(999, aLine.s, zLine.s);
			}
		wcnt = WordCount(aLine.s);
		if (wcnt == 0)
		{						/* ignore blank lines */
			if (wcnt == 1)
				SayError("Missing part type");
			continue;
		}
		theType = FindSym(GetWord(2, aLine.s));
		StrCpyCk(99, xWord.s, GetWord(1, aLine.s));
		if (theType == 8)
		{						/* force new spelling for hex labels.. */
			StrCatCk(99, xWord.s, " ");
			theName = FindSym(xWord.s);
		}
		else
			theName = FindSym(xWord.s);
		if (theName == 64)
		{						// /if (0==strcmp(theName.s,"*DB*")) {
			ix = IntOf(GetWord(3, aLine.s));
			if (ix > 0)
				RunDebug = ix;
			DEBUGGING = IntOf(SpellSym(theType));
			continue;
		}
		if (DEBUGGING > 1)
		{
			LogIt("*: ");
			LogNum(here);
			LogMo("-");
			LogNum(lino);
			LogMo(".");
			LogNum(wcnt);
			LogMo(" '");
			LogMo(aLine.s);
			LogMo("' ");
			LogNum(theType);
			LogOut();
		}
		here = Symbols[theType + NetDefn];
		if (theType == 60)
		{						/* -------------------------------------------------- 
								   END */
			if (NetIndex[inChip + 1] != theName)
			{
				SayError("Name mismatch in CHIP END ");
				LogMo(SpellSym(NetIndex[inChip + 1]));
				LogMo("/");
				LogMo(Listing.s);
				LogOut();
			}
			else
				NetIndex[inChip + 4] = NextNetx;
			if (inChip == 0)
				continue;
			front = 0;
			for (ix = NetIndex[inChip + 3]; ix < NextNetx;)
			{
				if (front == 0)
					front = ix;
				xi = NetIndex[ix++];
				if (xi == -1)
					front = 0;
				if (front > 0)
				{				/* undefine these symbols... */
					if (xi == 0 || xi == 1)
						if (NetIndex[ix] < -64)
						{
							xi = -NetIndex[ix];
							if (Symbols[xi + NetDefn] == front)
								Symbols[xi + NetDefn] = 0;
						}
					front = -1;
				}
			}
			inChip = 0;
		}
		else if (theType == 8)
		{						/* ---------------------------------------------- 
								   HEX */
			nbits = (wcnt + 1) / 4;	/* # columns of hex data to show */
			here = strlen(SpellSym(theName)) - 1;	/* # columns of header
													   text */
			if (DEBUGGING > 1)
			{
				LogIt(" HEX ");
				LogNum(nbits);
				LogMo(",");
				LogNum(here);
				LogOut();
			}
			if (here > nbits)
				here = here - nbits;	/* excess spaces to add to trace */
			else
				here = 0;
			TraceSize = TraceSize + nbits * 4 + here + 1;
			if (NextNetx + wcnt + 2 < MaxNet)
			{
				NetIndex[NextNetx++] = 2;
				NetIndex[NextNetx++] = theName;
				NetIndex[NextNetx++] = wcnt - 2;
				for (ix = 3; ix <= wcnt; ix++)
					NetIndex[NextNetx++] = FindSym(GetWord(ix, aLine.s));
				NetIndex[NextNetx++] = -1;
			}
			else
				StringOflo++;
		}
		else if (theType == 24)
		{						/* -------------------------------------------- 
								   DATA */
			/* Memory: #,addr,wait,dly,loc0,#locs,#data,#addr,inputs(a,w,d) */
			/* (mem) NetIndex:
			   4/5,name,link,MemAt,#data,#addr,Abits(BE)[,wr,Dbits(LE)] */
			/* NetIndex: 6,name,addr,#,data... */
			/* inMem = theName; <-- RAM/ROM did it, it's the Symbols name, not 
			   NetIndex */
			if (theName == 20 && RAMchip > 0)
			{
				inMem = RAMchip;
				RAMchip = 0;
				theName = 32;
			}
			else if (theName == 16 && ROMchip > 0)
			{
				inMem = ROMchip;
				ROMchip = 0;
				theName = 32;
			}
			if (MemSize == 0 || inMem == 0)
			{
				SayError("No ROM for this DATA: ");
				LogMo(Listing.s);
				LogOut();
				continue;
			}
			xi = Symbols[inMem + NetDefn];
			nbits = NetIndex[xi + 5];	/* # address bits */
			here = 1;
			for (ix = 0; ix < nbits; ix++)
				here = here * 2;
			front = Numify(SpellSym(theName), 0);
			if (DEBUGGING > 1)
			{
				LogIt(" DATA ");
				LogNum(here);
				LogMo(",");
				LogNum(front);
				LogOut();
			}
			if (front + wcnt - 3 > here)
			{
				SayError("DATA out of address space: ");
				LogMo(Listing.s);
				LogOut();
				continue;
			}
			NetIndex[NextNetx++] = 6;
			NetIndex[NextNetx++] = inMem;	/* name */
			NetIndex[NextNetx++] = front;
			NetIndex[NextNetx++] = wcnt - 2;
			if (DEBUGGING > 1)
			{
				StrCpyCk(999, zLine.s, SpellSym(NetIndex[xi + 1]));
				StrCatCk(99, zLine.s, "[");
				StrCatCk(999, zLine.s, StrOf(front));
				StrCatCk(99, zLine.s, "/");
				StrCatCk(999, zLine.s, StrOf(here));
				StrCatCk(99, zLine.s, "]");
			}
			nbits = NetIndex[xi + 4];	/* # data bits */
			for (ix = 3; ix <= wcnt; ix++)
			{
				xi = Numify(GetWord(ix, aLine.s), nbits);
				NetIndex[NextNetx++] = xi;
				if (DEBUGGING > 1)
				{
					StrCatCk(999, zLine.s, " ");
					StrCatCk(999, zLine.s, StrOf(xi));
				}
			}
			NetIndex[NextNetx++] = -1;
			if (DEBUGGING > 1)
			{
				LogIt("  -- ");
				LogMo(zLine.s);
				LogOut();
			}
		}
		else if (theName < 66)
		{
			SayError("Name is reserved: ");
			LogMo(Listing.s);
			LogOut();
		}
		else if (Symbols[theName + NetDefn] > 0)
		{
			SayError("Name already defined: ");
			LogMo(Listing.s);
			LogOut();
		}
		else if (NetIndex[here] == 3)
		{						/* ------------------------------ macro call.. 
								 */
			/* " name,ii,sssss,eeeee " -- i-10 inputs, start at s-100000 thru
			   e-100000 */
			StrCpyCk(99, aWord.s, SpellSym(theName));
			StrCatCk(99, aWord.s, ".0");
			ix = FindSym(aWord.s);
			Symbols[theName + NetDefn] = NextNetx;
			if (inChip > 0)
			{
				xi = -theName;
				ix = -ix;
			}
			else
				xi = theName;
			NetIndex[NextNetx++] = 0;
			NetIndex[NextNetx++] = xi;
			NetIndex[NextNetx++] = ix;
			NetIndex[NextNetx++] = -1;
			thar = NetIndex[here + 2];	/* = # inputs, rename them */
			/* note that inputs might be "+", which requires FindSym calls in
			   order */
			/* without intervening FindSym calls on other names: so split
			   for-loop */
			if (thar + 2 < wcnt)
			{
				SayError(" Excess inputs ignored: ");
				LogMo(Listing.s);
				LogOut();
			}
			else if (theType != RenumMacro)
				if (thar + 2 > wcnt)
				{
					SayError(" Undefined inputs set to X: ");
					LogMo(Listing.s);
					LogOut();
				}
			for (ix = 0; ix < thar; ix++)
			{					/* first make places for them */
				StrCpyCk(99, xWord.s, SpellSym(theName));
				StrCatCk(99, xWord.s, ".");
				StrCatCk(99, xWord.s, SpellSym(theType));
				StrCatCk(99, xWord.s, ".");
				StrCatCk(99, xWord.s, StrOf(ix));
				nbits = FindSym(xWord.s);
				Symbols[nbits + NetDefn] = NextNetx;
				NetIndex[NextNetx++] = 0;
				if (inChip > 0)
					NetIndex[NextNetx++] = -nbits;	/* former "~.a" is now -a */
				else
					NetIndex[NextNetx++] = nbits;
				NetIndex[NextNetx++] = 0;	/* xi goes here */
				NetIndex[NextNetx++] = -1;
			}
			NextNetx = NextNetx - thar * 4;
			for (ix = 0; ix < thar; ix++)
			{					/* then get the input names, in order.. */
				if (ix + 3 > wcnt)
					xi = 56;
				else
					xi = FindSym(GetWord(ix + 3, aLine.s));
				if (inChip > 0)
					if (xi > 64)
						xi = -xi;
				NextNetx = NextNetx + 2;
				NetIndex[NextNetx++] = xi;
				NextNetx++;
			}
			ix = NetIndex[here + 3];
			thar = NetIndex[here + 4];
			if (DEBUGGING > 1)
			{
				LogIt(" Macro ");
				LogNum(ix);
				LogMo(",");
				LogNum(here);
				LogOut();
			}
			front = 0;
			while (thar > ix)
			{					/* recopy macro lines to primary netlist as
								   renamed.. */
				if (front == 0)
				{
					nbits = 0;
					if (inChip == 0)
						if (NetIndex[ix] == 1)
						{
							nbits = NetSize;
							NetSize = NetSize + 2;
						}
					front = NextNetx;
				}
				xi = NetIndex[ix++];
				if (xi == -1)
					front = 0;
				if (xi < -1)
				{				/* substitute caller name for all "~".. */
					StrCpyCk(99, aWord.s, SpellSym(theName));
					StrCatCk(99, aWord.s, ".");
					StrCatCk(99, aWord.s, SpellSym(-xi));
					xi = FindSym(aWord.s);
					if (inChip > 0)
						xi = -xi;
				}				/* nested macro, preserve insertion */
				if (inChip == 0)
					if (front == -1)
						NetSize = NetSize + 1;
				if (front > 0 || front < -2)
					if (xi > 64)
						if (Symbols[xi + NetDefn] == 0)
						{
							if (DEBUGGING > 3)
							{
								LogIt(" ~ ");
								LogNum(front);
								LogMo(": ");
								LogNum(xi);
								LogMo("=");
								LogNum(nbits);
								LogOut();
							}
							if (front < 0)
								front = -front;
							Symbols[xi + NetDefn] = front;
							if (nbits > 0)
								Symbols[xi + GateNo] = nbits;
							nbits = 0;
							front = NetIndex[front] - 2;
						}		/* gate = -1; equ = -2 */
				NetIndex[NextNetx++] = xi;
			}					/* end while */
			nbits = 0;
		}
		else if (theType == 28)
		{						/* -------------------------------- binding
								   post.. = */
			if (DEBUGGING > 1)
				LogIt(" Equate ");
			if (3 < wcnt)
			{
				SayError(" Excess inputs ignored: ");
				LogMo(Listing.s);
				LogOut();
			}
			ix = FindSym(GetWord(3, aLine.s));
			Symbols[theName + NetDefn] = NextNetx;
			if (inChip > 0)
			{
				xi = -theName;
				if (ix > 64)
					ix = -ix;
			}
			else
				xi = theName;
			NetIndex[NextNetx++] = 0;
			NetIndex[NextNetx++] = xi;
			NetIndex[NextNetx++] = ix;
			NetIndex[NextNetx++] = -1;
		}
		else if (theType == 4)
		{						/* --------------------------------------------- 
								   GATE */
			if (DEBUGGING > 1)
			{
				LogIt(" GATE ");
				LogNum(NextNetx);
				LogMo(" - ");
				LogNum(NetSize);
			}
			Symbols[theName + NetDefn] = NextNetx;
			if (inChip == 0)
			{
				Symbols[theName + GateNo] = NetSize;
				NetSize = NetSize + wcnt + 1;
				xi = theName;
			}
			else
				xi = -theName;
			NetIndex[NextNetx++] = 1;
			NetIndex[NextNetx++] = xi;
			NetIndex[NextNetx++] = wcnt - 2;
			for (ix = 3; ix <= wcnt; ix++)
			{
				xi = FindSym(GetWord(ix, aLine.s));
				if (inChip > 0)
					if (xi > 64)
						xi = -xi;
				NetIndex[NextNetx++] = xi;
			}
			NetIndex[NextNetx++] = -1;
		}
		else if (inChip > 0)
		{						/* ------------------------------------ within 
								   macro defn.. */
			SayError("Invalid CHIP component: ");
			LogMo(Listing.s);
			LogOut();
		}
		else if (theType == 12)
		{						/* ------------------------------- macro
								   defn.. CHIP */
			if (wcnt > 2)
			{
				StrCpyCk(99, aWord.s, GetWord(3, aLine.s));
				ix = IntOf(aWord.s);
			}
			else
				ix = 0;
			here = NextNetx;
			if (DEBUGGING > 1)
			{
				LogIt(" CHIP ");
				LogNum(ix);
				LogMo(",");
				LogNum(here);
				LogOut();
			}
			/* " name,ii,ss,ee " -- ii inputs, start at ss thru ee */
			inChip = NextNetx;
			Symbols[theName + NetDefn] = NextNetx;
			NetIndex[NextNetx++] = 3;
			NetIndex[NextNetx++] = theName;
			NetIndex[NextNetx++] = ix;	/* # inputs */
			NetIndex[NextNetx++] = inChip + wcnt + 4;
			NetIndex[NextNetx++] = 000;	/* to be filled at end */
			NetIndex[NextNetx++] = wcnt - 3;	/* # outputs */
			for (ix = 4; ix <= wcnt; ix++)
			{
				xi = FindSym(GetWord(ix, aLine.s));	/* each output.. */
				if (xi == 0)
					xi = 56;
				NetIndex[NextNetx++] = xi;
			}
			NetIndex[NextNetx++] = -1;
			for (ix = 0; ix < wcnt - 3; ix++)
			{
				xi = NetIndex[inChip + ix + 6];	/* set up '~.i = ~o.i' */
				if (xi > 64)
					xi = -xi;
				NetIndex[NextNetx++] = 0;
				NetIndex[NextNetx++] = -FindSym(StrOf(ix));
				NetIndex[NextNetx++] = xi;
				NetIndex[NextNetx++] = -1;
			}
		}
		else if (theType == 20)
		{						/* --------------------------------------------- 
								   RAM */
			/* name,RAM,#data,addr list (BE'n),write,data list (LE'n) */
			inMem = theName;
			if (RAMchip == 0)
				RAMchip = inMem;
			nbits = IntOf(GetWord(3, aLine.s));	/* # data bits */
			front = wcnt - 4 - nbits;	/* # address bits */
			if (front <= 0)
			{
				SayError("No address bits ");
				LogMo(Listing.s);
				LogOut();
				continue;
			}
			here = 1;			/* will be size.. */
			for (ix = 0; ix < front; ix++)
				here = here * 2;
			if (DEBUGGING > 1)
			{
				LogIt(" RAM ");
				LogNum(nbits);
				LogMo("x");
				LogNum(here);
				LogOut();
			}
			Symbols[theName + NetDefn] = NextNetx;
			if (MemList == 0)
				MemList = NextNetx;
			if (MemTail > 0)
				NetIndex[MemTail + 2] = NextNetx;
			MemTail = NextNetx;
			NetIndex[NextNetx++] = 5;
			NetIndex[NextNetx++] = theName;
			NetIndex[NextNetx++] = 0;	/* new memory list tail */
			NetIndex[NextNetx++] = 0;	/* mem loc */
			NetIndex[NextNetx++] = nbits;	/* # data bits */
			NetIndex[NextNetx++] = front;	/* # address bits */
			for (ix = 4; ix <= wcnt; ix++)	// Adr:4..; Wr:front+4; Dat:..wcnt
				NetIndex[NextNetx++] = FindSym(GetWord(ix, aLine.s));	/* each 
																		   addr/data 
																		 */
			NetIndex[NextNetx++] = -1;
			for (ix = 0; ix < nbits; ix++)
			{
				StrCpyCk(99, aWord.s, SpellSym(theName));
				StrCatCk(99, aWord.s, ".");
				StrCatCk(99, aWord.s, StrOf(ix));
				xi = FindSym(aWord.s);
				Symbols[xi + GateNo] = NetSize;
				NetSize = NetSize + 5;
				Symbols[xi + NetDefn] = NextNetx;
				NetIndex[NextNetx++] = 7;	/* memory data bit */
				NetIndex[NextNetx++] = xi;
				NetIndex[NextNetx++] = MemTail;
				NetIndex[NextNetx++] = 0;	/* for netlist place */
				NetIndex[NextNetx++] = -1;
			}
			if (nbits < 1 || nbits > 32 || front > 16 || front < 1)
			{
				SayError("Invalid address or data size: ");
				LogMo(Listing.s);
				LogOut();
			}
			nbits = here;		/* max data */
			MemSize = MemSize + here + wcnt + 7;
		}
		else if (theType == 16)
		{						/* --------------------------------------------- 
								   ROM */
			/* name,ROM,#data,addr list (BigEndian) */
			inMem = theName;
			if (ROMchip == 0)
				ROMchip = inMem;
			nbits = IntOf(GetWord(3, aLine.s));	/* # data bits */
			front = wcnt - 3;	/* # address bits */
			here = 1;			/* will be size.. */
			for (ix = 0; ix < front; ix++)
				here = here * 2;
			if (DEBUGGING > 1)
			{
				LogIt(" ROM ");
				LogNum(nbits);
				LogMo(",");
				LogNum(here);
				LogOut();
			}
			Symbols[theName + NetDefn] = NextNetx;
			if (MemList == 0)
				MemList = NextNetx;
			if (MemTail > 0)
				NetIndex[MemTail + 2] = NextNetx;
			MemTail = NextNetx;
			NetIndex[NextNetx++] = 4;
			NetIndex[NextNetx++] = theName;
			NetIndex[NextNetx++] = 0;	/* new memory list tail */
			NetIndex[NextNetx++] = 0;	/* mem loc */
			NetIndex[NextNetx++] = nbits;	/* # data bits */
			NetIndex[NextNetx++] = front;	/* # address bits */
			for (ix = 4; ix <= wcnt; ix++)
				NetIndex[NextNetx++] = FindSym(GetWord(ix, aLine.s));	/* each 
																		   address 
																		 */
			NetIndex[NextNetx++] = -1;
			for (ix = 0; ix < nbits; ix++)
			{
				StrCpyCk(99, aWord.s, SpellSym(theName));
				StrCatCk(99, aWord.s, ".");
				StrCatCk(99, aWord.s, StrOf(ix));
				xi = FindSym(aWord.s);
				Symbols[xi + GateNo] = NetSize;
				NetSize = NetSize + 5;
				Symbols[xi + NetDefn] = NextNetx;
				NetIndex[NextNetx++] = 7;	/* memory data bit */
				NetIndex[NextNetx++] = xi;
				NetIndex[NextNetx++] = MemTail;
				NetIndex[NextNetx++] = 0;	/* for netlist place */
				NetIndex[NextNetx++] = -1;
			}
			if (nbits < 1 || nbits > 32 || front > 16 || front < 1)
			{
				SayError("Invalid address or data size: ");
				LogMo(Listing.s);
				LogOut();
			}
			nbits = here;		/* max data */
			MemSize = MemSize + here + wcnt + nbits + 8;
		}
		else if (IntOf(SpellSym(theType)) > 0)
		{						/* -------------------- clock specs.. */
			doClox = -IntOf(SpellSym(theName));	/* run, ClockRate, PonDelay,
												   Trate, TraPh */
			if (doClox >= 0)
				doClox = -1;
			ClockRate = IntOf(SpellSym(theType));
			if (ClockRate <= 0)
				ClockRate = 1;
			PonDelay = IntOf(GetWord(3, aLine.s)) * ClockRate + 2;
			TraPh = IntOf(GetWord(5, aLine.s));
			if (TraPh < 0)
				TraPh = 0;
			StrCpyCk(99, aWord.s, GetWord(4, aLine.s));
			Trate = IntOf(aWord.s);
			if (Trate < 0)
				TraceGate = FindSym(aWord.s);
			if (DEBUGGING > 1)
			{
				LogIt(" doClox=");
				LogNum(doClox);
				LogMo(" ClockRate=");
				LogNum(ClockRate);
				LogIt(" PonDelay=");
				LogNum(PonDelay);
				LogMo(" Trate=");
				LogMo(aWord.s);
				LogMo("=");
				LogNum(Trate);
				LogMo(" TraPh=");
				LogNum(TraPh);
				LogOut();
			}
		}
		else
		{
			SayError("Unknown part type: ");
			LogMo(Listing.s);
			LogOut();
			continue;
		}
	}							/* end while (lino<DataLen) */
	if (inChip > 0)
		SayError("Missing CHIP END");
}								/* end DataIn */

void BuildNet(void)
{								/* construct actual gate array
								   NetList[NetAt++] from NetIndex.. */
	int ix, lino, here, thar, wcnt, nbits, whom;
	SmallString aWord;
	int ngates = 0;
	/* NetIndex formats: 0,s,n,-1 equate s=n (both symbol index)
	   1,s,#,i1,i2,i3..,-1 gate, name, #ins, i's are symbol indices
	   2,n,#,i1,i2,..,-1 hex, name, #ins, i's are symbol indices
	   3,s,#,b,e,#,o1,o2..,-1 macro, #ins, beginx,endx, #outs, outs
	   4,s,lk,#,#,#,..,a2,a1,a0,-1 rom,name,lnk,m#,#data,#adr,adrlst(BE'n)
	   5,s,lk,#,#,#,..,a1,a0,w,d0,d1..
	   nm,lk,m#,#d,#a,adrlst(BE'n),wr,dlst(LE'n) 6,m,a,#,d,d,d,d,..  data,
	   memname, addr, #data, data list 7,n,m,-1 data bit in memory m */
	if (DEBUGGING > 2)
	{
		LogIt("");
		LogIt("BuildNet:");
	}
	Pacify(10000, "");
	thar = 0;
	for (lino = 0; lino < NextNetx;)
	{
		if (NetIndex[lino++] != -1)
		{
			SayError("Oops, NetIndex-1");
			break;
		}
		whom = NetIndex[lino++];
		switch (whom)
		{
		case 0:				/* -------------------------------------------------------- 
								   equate */
			if (DEBUGGING > 3)
				if (NetIndex[lino] > 0)
				{
					LogIt("");
					LogNum(lino - 1);
					LogMo(" EQU ");
					LogMo(SpellSym(NetIndex[lino]));
					LogMo(" = ");
					LogMo(SpellSym(NetIndex[lino + 1]));
					LogOut();
				}
			lino = lino + 2;
			break;
		case 1:				/* ---------------------------------------------------------- 
								   gate */
			Pacify(0, " nodes connected");
			ix = NetIndex[lino++];	/* name */
			nbits = NetIndex[lino++];	/* # ins */
			if (ix > 0)
			{
				ngates = ngates + 1;
				if (DEBUGGING > 1)
				{
					LogIt("");
					LogNum(lino - 3);
					LogMo(" GATE ");
					LogNum(NetAt);
					LogMo("= ");
					LogMo(SpellSym(ix));
					LogOut();
				}
				if (Symbols[ix + GateNo] != NetAt)
				{
					if (ErrCount * 2 < ErrMaxOff)
						SayError("? ");
					LogMo("Gate Off: ");
					LogNum(Symbols[ix + GateNo]);
					LogMo("/");
					LogNum(NetAt);
					LogOut();
					NetAt = Symbols[ix + GateNo];
					if (thar > 0)
						NetList[thar] = NetAt - thar;
				}
				NetInvert[NetAt] = ix & 255;
				thar = NetAt++;
				NetInvert[NetAt] = (ix >> 8) & 255;
				NetList[NetAt++] = -1;
				NetInvert[NetAt] = ix >> 16;
				NetList[NetAt++] = -1;
				for (ix = 0; ix < nbits; ix++)
					NetList[NetAt++] = FindNode(NetIndex[lino++], "gate");
				NetList[thar] = NetAt - thar;
				if (NetSize < NetAt)
					SayError("Net O'flo");
			}
			else
				lino = lino + nbits;	/* skip over macro lines */
			break;
		case 2:				/* ----------------------------------------------------------- 
								   hex */
			ix = NetIndex[lino++];	/* name */
			wcnt = NetIndex[lino++];
			nbits = (wcnt + 3) / 4;	/* # columns of hex data to show */
			StrCpyCk(99, aWord.s, SpellSym(ix));
			here = strlen(aWord.s) - 1;	/* # columns of header text */
			SubStrCpy(aWord.s, aWord.s, 0, here);	/* trim off final space */
			if (DEBUGGING > 2)
			{
				LogIt("");
				LogNum(lino - 3);
				LogMo(" HEX ");
				LogNum(TraceAt);
				LogMo(" ");
				LogNum(here);
				LogMo("/");
				LogNum(nbits);
				LogMo(" ");
				LogMo(SpellSym(ix));
				LogOut();
			}
			while (nbits > here)
			{
				if (((nbits - (here++)) & 1) > 0)
				{
					StrCpyCk(99, zWord.s, " ");
					StrCatCk(99, zWord.s, aWord.s);
				}
				else
				{
					StrCpyCk(99, zWord.s, aWord.s);
					StrCatCk(99, zWord.s, " ");
				}
				StrCpyCk(99, aWord.s, zWord.s);
			}
			if (strlen(Headers.s) + strlen(aWord.s) < 999)
			{
				StrCatCk(999, Headers.s, aWord.s);
				StrCatCk(999, Headers.s, " ");
			}
			for (ix = here - nbits; ix > 0; ix = ix - 2)
				TraceList[TraceAt++] = -1;	/* spaces */
			for (ix = 3 - ((wcnt + 3) & 3); ix > 0; ix--)
				TraceList[TraceAt++] = 0;
			for (ix = 0; ix < wcnt; ix++)
				TraceList[TraceAt++] = FindNode(NetIndex[lino++], "hex");
			for (ix = here - nbits - 1; ix > 0; ix = ix - 2)
				TraceList[TraceAt++] = -1;
			TraceList[TraceAt++] = -1;
			if (TraceSize < TraceAt)
				SayError("Trace O'flo");
			break;
		case 3:				/* --------------------------------------------------------- 
								   macro */
			if (DEBUGGING > 3)
			{
				LogIt("");
				LogNum(lino - 1);
				LogMo(" CHIP ");
				LogMo(SpellSym(NetIndex[lino]));
				LogOut();
			}
			lino = lino + NetIndex[lino + 4] + 5;
			break;
		case 4:				/* ----------------------------------------------------------- 
								   rom */
			/* rom, name, #data, #adr, addr list (BigEndian) */
			/* Memory: #,addr,wait,dly,loc0,#locs,#data,#addr,inputs(a,w,d) */
			/* NetIndex: 4,name,link,MemAt,#data,#addr,Abits(BE) */
			whom = NetIndex[lino++];	/* name */
			lino++;				/* list link */
			Memory[MemAt++] = whom;
			NetIndex[lino++] = MemAt;	/* mem loc */
			Memory[0] = MemAt;
			nbits = NetIndex[lino++];	/* # data bits */
			wcnt = NetIndex[lino++];	/* # address bits */
			here = 1;			/* will be size.. */
			for (ix = 0; ix < wcnt; ix++)
				here = here * 2;
			if (DEBUGGING > 1)
			{
				LogIt("");
				LogNum(lino - 6);
				LogMo(" ROM ");
				LogMo(SpellSym(whom));
				LogMo(" ");
				LogNum(NetAt);
				LogMo("/");
				LogNum(MemAt);
				LogMo("/");
				LogNum(DataAt - here);
				LogMo(" ");
				LogNum(nbits);
				LogMo("~");
				LogNum(here);
				LogOut();
			}
			thar = NetAt;		/* save this for NetInvert in immediately
								   following membit */
			for (ix = 0; ix < nbits; ix++)
			{
				NetList[NetAt++] = 5;
				NetList[NetAt++] = -1;
				NetList[NetAt++] = -1;
				NetList[NetAt++] = -MemAt;
				NetList[NetAt++] = ix;
			}
			if (NetSize < NetAt)
				SayError("Net O'flo");
			for (ix = 0; ix <= here; ix++)
				Memory[--DataAt] = UndefinedMem;
			ix = (wcnt + 2) / 5;
			ix = ix * ix + 4;	/* read/write access delay */
			Memory[MemAt++] = wcnt + nbits + 9;
			Memory[MemAt++] = -1;
			Memory[MemAt++] = -1;
			Memory[MemAt++] = ix;
			Memory[MemAt++] = DataAt;
			Memory[MemAt++] = here;
			Memory[MemAt++] = nbits;
			Memory[MemAt++] = wcnt;
			for (ix = 0; ix < wcnt; ix++)
				Memory[MemAt++] = FindNode(NetIndex[lino++], "rom");
			Memory[MemAt++] = 1;
			for (ix = 0; ix < nbits; ix++)
				Memory[MemAt++] = 10;
			if (DataAt < MemAt)
				SayError("Memory O'flo");
			break;
		case 5:				/* ----------------------------------------------------------- 
								   ram */
			/* RAM,name,#data,#adr,addr list (BE'n),write,data list (LE'n) */
			/* Memory: #,addr,wait,dly,loc0,#locs,#data,#addr,inputs(a,w,d) */
			/* NetIndex: 5,name,link,MemAt,#data,#addr,Abits(BE),wr,Dbits(LE) */
			whom = NetIndex[lino++];	/* name */
			lino++;				/* list link, used by DumpIt */
			Memory[MemAt++] = whom;
			NetIndex[lino++] = MemAt;	/* mem loc */
			Memory[0] = MemAt;
			nbits = NetIndex[lino++];	/* # data bits */
			wcnt = NetIndex[lino++];	/* # address bits */
			here = 1;			/* will be size.. */
			for (ix = 0; ix < wcnt; ix++)
				here = here * 2;
			if (DEBUGGING > 1)
			{
				LogIt("");
				LogNum(lino - 6);
				LogMo(" RAM ");
				LogMo(SpellSym(whom));
				LogMo(" ");
				LogNum(NetAt);
				LogMo("/");
				LogNum(MemAt);
				LogMo("/");
				LogNum(DataAt - here);
				LogMo(" ");
				LogNum(nbits);
				LogMo("~");
				LogNum(here);
				LogOut();
			}
			thar = NetAt;		/* save this for NetInvert in immediately
								   following membit */
			for (ix = 0; ix < nbits; ix++)
			{
				NetList[NetAt++] = 5;
				NetList[NetAt++] = -1;
				NetList[NetAt++] = -1;
				NetList[NetAt++] = -MemAt;
				NetList[NetAt++] = ix;
			}
			if (NetSize < NetAt)
				SayError("Net O'flo");
			for (ix = 0; ix <= here; ix++)
				Memory[--DataAt] = UndefinedMem;
			ix = (wcnt + 2) / 5;
			ix = ix * ix + 4;	/* read/write access delay */
			Memory[MemAt++] = wcnt + nbits + 9;
			Memory[MemAt++] = -1;
			Memory[MemAt++] = -1;
			Memory[MemAt++] = ix;
			Memory[MemAt++] = DataAt;
			Memory[MemAt++] = here;
			Memory[MemAt++] = nbits;
			Memory[MemAt++] = wcnt;
			for (ix = 0; ix <= nbits + wcnt; ix++)
				Memory[MemAt++] = FindNode(NetIndex[lino++], "ram");
			if (DataAt < MemAt)
				SayError("Memory O'flo");
			break;
		case 6:				/* ---------------------------------------------------------- 
								   data */
			/* Memory: #,addr,wait,dly,loc0,#locs,#data,#addr,inputs(a,w,d) */
			/* NetIndex: 6,name,addr,#,data... */
			whom = NetIndex[lino++];	/* mem name */
			thar = NetIndex[Symbols[whom + NetDefn] + 3];	/* mem info base */
			here = Memory[thar + 4];	/* loc0 */
			here = here + NetIndex[lino++];	/* address */
			if (DEBUGGING > 2)
			{
				LogIt("");
				LogNum(lino - 3);
				LogMo(" DATA ");
				LogNum(thar);
				LogMo("`");
				LogMo(SpellSym(whom));
				LogMo(" @");
				LogNum(here);
				LogOut();
			}
			for (ix = NetIndex[lino++]; ix > 0; ix--)
				Memory[here++] = NetIndex[lino++];
			break;
		case 7:				/* -------------------------------------------------------- 
								   membit */
			whom = NetIndex[lino++];	/* name */
			here = NetIndex[lino++];	/* mem ref */
			NetIndex[lino++] = thar;
			if (DEBUGGING > 2)
			{
				LogIt("");
				LogNum(lino - 4);
				LogMo(" MBIT ");
				LogNum(thar);
				LogMo(" =");
				LogMo(SpellSym(whom));
				LogMo(" % ");
				LogNum(here);
				LogOut();
			}
			for (ix = 0; ix < 5; ix++)
			{
				NetInvert[thar++] = whom & 255;
				whom = whom >> 8;
			}
			break;
		default:
			SayError("Oops, NetIndex??");
			continue;
		}
	}							/* end switch, end for */
	Pacify(-1, " nodes total, for ");
	LogNum(ngates);
	LogMo(" gates");
	LogIt("");
	LogOut();
}								/* end BuildNet */

int FindNode(int theRef, char *whom)
{								/* look theRef up in Symbols */
	int here;
	int reref = theRef;
	while (true)
	{
		here = Symbols[reref + NetDefn];
		if (reref > 66 && here == 0)
		{
			SayError("Undefined gate name in ");
			LogMo(whom);
			LogMo(": ");
			LogMo(SpellSym(reref));
			LogOut();
			return 10;
		}
		else if (NetIndex[here] == 1 || NetIndex[here] == 7 || reref < 60
				 && reref > 25)
		{
			return Symbols[reref + GateNo];
		}
		else if (NetIndex[here] == 0)
		{
			reref = NetIndex[here + 2];
			if (reref < 1)
			{
				SayError("Oops equ (in ");
				LogMo(whom);
				LogMo("/");
				LogNum(theRef);
				LogMo("): ");
				LogNum(here);
				LogMo("=");
				LogNum(reref);
				LogOut();
				return 10;
			}
			else
				continue;
		}
		else
		{
			SayError("Oops net (in ");
			LogMo(whom);
			LogMo("/");
			LogNum(theRef);
			LogMo("): ");
			if (reref != theRef)
			{
				LogNum(reref);
				LogMo("->");
			}
			LogNum(here);
			LogMo("=");
			LogNum(NetIndex[here]);
			LogOut();
			return 10;
		}
	}							/* end while true */
}								/* end FindNode */

void SayError(char *theMsg)
{								/* error checking.. */
	if (*theMsg != ' ')
	{
		ErrCount++;
		LogIt("*** ");
	}
	else
		LogIt("--- ");
	LogMo(theMsg);
	/* if (DEBUGGING>5) PanicDump(); */
	if (ErrCount > ErrMaxOff)
	{
		LogOut();
		exit(1);
	}
}								/* end SayError */

void CheckOflo(int is, int mx, char *sayso)
{
	if (is < mx - (mx >> 3))
		return;
	SayError(sayso);
	LogMo(" filled to ");
	LogNum(is * 100 / mx + 1);
	LogMo("% full.");
	LogOut();
}

int WordCount(char *theStr)
{								/* count the words in theStr */
	int ix;
	SmallString aStr;
	for (ix = 1; true; ix++)
	{
		StrCpyCk(99, aStr.s, GetWord(ix, theStr));
		if (strlen(aStr.s) == 0)
			return ix - 1;
	}
}								/* end WordCount */

char *GetWord(int wdno, char *theStr)
{								/* return word #wdno from theStr */
	int maxey, inWd, ix;
	maxey = strlen(theStr);
	inWd = false;
	WdOffs = -1;				/* global, returns offset to selected word; -1 
								   if none */
	for (ix = 0; ix < maxey; ix++)
	{
		if (theStr[ix] <= ' ')
		{
			if (WdOffs >= 0)
			{
				maxey = ix;
				break;
			}
			inWd = false;
		}
		else if (!inWd)
		{
			if (--wdno == 0)
				WdOffs = ix;
			inWd = true;
		}
	}
	if (DEBUGGING > 4)
	{
		LogIt("   @");
		LogNum(WdOffs);
		LogMo("/");
		LogNum(maxey);
		LogOut();
	}
	if (WdOffs >= 0)
		return SubStr(theStr, WdOffs, maxey);
	return "";
}								/* end GetWord */

int Numify(char *theStr, int nbits)
{								/* convert hex/bin/dec to int */
	int ix, theNum, len, ch;	/* theStr could be decimal or hex or binary.. */
	theNum = 0;
	len = strlen(theStr);
	if (len == nbits)			/* binary, just look at low bit.. */
		for (ix = 0; ix < len; ix++)
			theNum = theNum * 2 + ((int)(theStr[ix] & 1));
	else if (theStr[0] == '0')
		for (ix = 0; ix < len; ix++)
		{
			ch = (int)theStr[ix];
			if (ch == (int)'x')
				continue;
			if (ch < 58)
				ch = ch & 15;
			else
				ch = (ch & 7) + 9;
			theNum = theNum * 16 + ch;
		}
	else
		theNum = IntOf(theStr);
	return theNum;
}								/* end Numify */

void InitMacros(void)
{
	char MacData[10000];
	StrCpyCk(99, MacData, "; Predefined Macros\r");
	StrCatCk(9999, MacData, "Renum chip 32 Renum.0 + + + + + + +");
	StrCatCk(9999, MacData,
			 "  + + + + + + + +  + + + + + + + +  + + + + + + + +\r");
	StrCatCk(9999, MacData, "Renum end\r");	/* renumbers its inputs, 0..31 */
	StrCatCk(9999, MacData, "Pulse chip 1 p0 t2 p1\r");	/* rising edge */
	StrCatCk(9999, MacData, "i1 gate Pulse.0\r");
	StrCatCk(9999, MacData, "i2 gate i1\r");
	StrCatCk(9999, MacData, "i3 gate i2\r");
	StrCatCk(9999, MacData, "p0 gate Pulse.0 i3\r");
	StrCatCk(9999, MacData, "p1 gate p0\r");
	StrCatCk(9999, MacData, "t1 gate p0 t2\r");
	StrCatCk(9999, MacData, "t2 gate TRACED t1\r");
	StrCatCk(9999, MacData, "Pulse end\r");
	StrCatCk(9999, MacData, "Add chip 3 Cy Sum\r");	/* A B Ci */
	StrCatCk(9999, MacData, "Sum gate abc ao bo co\r");
	StrCatCk(9999, MacData, "Cy  gate ab ac bc\r");
	StrCatCk(9999, MacData, "abc gate Add.0 Add.1 Add.2\r");
	StrCatCk(9999, MacData, "ab  gate Add.0 Add.1\r");
	StrCatCk(9999, MacData, "ac  gate Add.0 Add.2\r");
	StrCatCk(9999, MacData, "bc  gate Add.1 Add.2\r");
	StrCatCk(9999, MacData, "ao  gate Add.0 ab ac\r");
	StrCatCk(9999, MacData, "bo  gate Add.1 ab bc\r");
	StrCatCk(9999, MacData, "co  gate Add.2 ac bc\r");
	StrCatCk(9999, MacData, "Add end\r");
	StrCatCk(9999, MacData, "FF chip 2 Q Q/\r");	/* D L (_/~\_) */
	StrCatCk(9999, MacData, "Q   gate Q/ mqg\r");
	StrCatCk(9999, MacData, "Q/  gate Q nqg\r");
	StrCatCk(9999, MacData, "mqg gate Ld/ mq\r");
	StrCatCk(9999, MacData, "nqg gate Ld/ nq\r");
	StrCatCk(9999, MacData, "mq  gate nq dg\r");
	StrCatCk(9999, MacData, "nq  gate mq ndg RESET\r");
	StrCatCk(9999, MacData, "dg  gate FF.0 FF.1 RESET\r");
	StrCatCk(9999, MacData, "ndg gate dg FF.1\r");
	StrCatCk(9999, MacData, "Ld/ gate FF.1\r");
	StrCatCk(9999, MacData, "FF end\r");
	StrCatCk(9999, MacData, "Cnt4 chip 6 Q0.0 Q1.0 Q2.0 Q3.0\r");	/* D0 D1
																	   D2 D3
																	   Cnt CLK 
																	 */
	StrCatCk(9999, MacData, "l0  gate ld Cnt4.0\r");
	StrCatCk(9999, MacData, "l1  gate ld Cnt4.1\r");
	StrCatCk(9999, MacData, "l2  gate ld Cnt4.2\r");
	StrCatCk(9999, MacData, "l3  gate ld Cnt4.3\r");
	StrCatCk(9999, MacData, "Q0  FF D0 Cnt4.5\r");
	StrCatCk(9999, MacData, "Q1  FF D1 Cnt4.5\r");
	StrCatCk(9999, MacData, "Q2  FF D2 Cnt4.5\r");
	StrCatCk(9999, MacData, "Q3  FF D3 Cnt4.5\r");
	StrCatCk(9999, MacData, "D0  gate c0 l0\r");
	StrCatCk(9999, MacData, "D1  gate c1 s1 l1\r");
	StrCatCk(9999, MacData, "D2  gate c2 s2 t2 l2\r");
	StrCatCk(9999, MacData, "D3  gate c3 s3 t3 u3 l3\r");
	StrCatCk(9999, MacData, "c0  gate Q0.1 Cnt4.4\r");
	StrCatCk(9999, MacData, "c1  gate Q1.1 Q0.0 Cnt4.4\r");
	StrCatCk(9999, MacData, "c2  gate Q2.1 Q0.0 Q1.0 Cnt4.4\r");
	StrCatCk(9999, MacData, "c3  gate Q3.1 Q0.0 Q1.0 Q2.0 Cnt4.4\r");
	StrCatCk(9999, MacData, "s1  gate Q1.0 Q0.1 Cnt4.4\r");
	StrCatCk(9999, MacData, "s2  gate Q2.0 Q1.1 Cnt4.4\r");
	StrCatCk(9999, MacData, "s3  gate Q3.0 Q2.1 Cnt4.4\r");
	StrCatCk(9999, MacData, "t2  gate Q2.0 Q0.1 Cnt4.4\r");
	StrCatCk(9999, MacData, "t3  gate Q3.0 Q1.1 Cnt4.4\r");
	StrCatCk(9999, MacData, "u3  gate Q3.0 Q0.1 Cnt4.4\r");
	StrCatCk(9999, MacData, "ld  gate Cnt4.4\r");
	StrCatCk(9999, MacData, "Cnt4 end\r");
#if AllMacros
	StrCatCk(9999, MacData, "Mux1 chip 3 Out\r");	/* A0 D0 D1 */
	StrCatCk(9999, MacData, "n0  gate Mux1.0\r");
	StrCatCk(9999, MacData, "s0  gate n0 Mux1.1\r");
	StrCatCk(9999, MacData, "s1  gate Mux1.0 Mux1.2\r");
	StrCatCk(9999, MacData, "Out gate s0 s1\r");
	StrCatCk(9999, MacData, "Mux1 end\r");
	StrCatCk(9999, MacData, "Mux2 chip 6 Out\r");	/* A0 A1 D0 D1 D2 D3 */
	StrCatCk(9999, MacData, "n0  gate Mux2.0\r");
	StrCatCk(9999, MacData, "n1  gate Mux2.1\r");
	StrCatCk(9999, MacData, "s0  gate n0 n1 Mux2.2\r");
	StrCatCk(9999, MacData, "s1  gate Mux2.0 n1 Mux2.3\r");
	StrCatCk(9999, MacData, "s2  gate n0 Mux2.1 Mux2.4\r");
	StrCatCk(9999, MacData, "s3  gate Mux2.0 Mux2.1 Mux2.5\r");
	StrCatCk(9999, MacData, "Out gate s0 s1 s2 s3\r");
	StrCatCk(9999, MacData, "Mux2 end\r");
	StrCatCk(9999, MacData, "Mux3 chip 11 Out\r");	/* A0 A1 A2 D0 D1 D2 D3 D4 
													   D5 D6 D7 */
	StrCatCk(9999, MacData, "n0  gate Mux3.0\r");
	StrCatCk(9999, MacData, "n1  gate Mux3.1\r");
	StrCatCk(9999, MacData, "n2  gate Mux3.2\r");
	StrCatCk(9999, MacData, "s0  gate n0 n1 n2 Mux3.3\r");
	StrCatCk(9999, MacData, "s1  gate Mux3.0 n1 n2 Mux3.4\r");
	StrCatCk(9999, MacData, "s2  gate n0 Mux3.1 n2 Mux3.5\r");
	StrCatCk(9999, MacData, "s3  gate Mux3.0 Mux3.1 n2 Mux3.6\r");
	StrCatCk(9999, MacData, "s4  gate n0 n1 Mux3.2 Mux3.7\r");
	StrCatCk(9999, MacData, "s5  gate Mux3.0 n1 Mux3.2 Mux3.8\r");
	StrCatCk(9999, MacData, "s6  gate n0 Mux3.1 Mux3.2 Mux3.9\r");
	StrCatCk(9999, MacData, "s7  gate Mux3.0 Mux3.1 Mux3.2 Mux3.10\r");
	StrCatCk(9999, MacData, "Out gate s0 s1 s2 s3 s4 s5 s6 s7\r");
	StrCatCk(9999, MacData, "Mux3 end\r");
	StrCatCk(9999, MacData, "Mux4 chip 20 Out\r");	/* A0 A1 A2 A3 D0 ... D15 */
	StrCatCk(9999, MacData, "n0  gate Mux4.0\r");
	StrCatCk(9999, MacData, "n1  gate Mux4.1\r");
	StrCatCk(9999, MacData, "n2  gate Mux4.2\r");
	StrCatCk(9999, MacData, "n3  gate Mux4.3\r");
	StrCatCk(9999, MacData, "s0  gate n0 n1 n2 n3 Mux4.4\r");
	StrCatCk(9999, MacData, "s1  gate Mux4.0 n1 n2 n3 Mux4.5\r");
	StrCatCk(9999, MacData, "s2  gate n0 Mux4.1 n2 n3 Mux4.6\r");
	StrCatCk(9999, MacData, "s3  gate Mux4.0 Mux4.1 n2 n3 Mux4.7\r");
	StrCatCk(9999, MacData, "s4  gate n0 n1 Mux4.2 n3 Mux4.8\r");
	StrCatCk(9999, MacData, "s5  gate Mux4.0 n1 Mux4.2 n3 Mux4.9\r");
	StrCatCk(9999, MacData, "s6  gate n0 Mux4.1 Mux4.2 n3 Mux4.10\r");
	StrCatCk(9999, MacData, "s7  gate Mux4.0 Mux4.1 Mux4.2 n3 Mux4.11\r");
	StrCatCk(9999, MacData, "s8  gate n0 n1 n2 Mux4.3 Mux4.12\r");
	StrCatCk(9999, MacData, "s9  gate Mux4.0 n1 n2 Mux4.3 Mux4.13\r");
	StrCatCk(9999, MacData, "s10 gate n0 Mux4.1 n2 Mux4.3 Mux4.14\r");
	StrCatCk(9999, MacData, "s11 gate Mux4.0 Mux4.1 n2 Mux4.3 Mux4.15\r");
	StrCatCk(9999, MacData, "s12 gate n0 n1 Mux4.2 Mux4.3 Mux4.16\r");
	StrCatCk(9999, MacData, "s13 gate Mux4.0 n1 Mux4.2 Mux4.3 Mux4.17\r");
	StrCatCk(9999, MacData, "s14 gate n0 Mux4.1 Mux4.2 Mux4.3 Mux4.18\r");
	StrCatCk(9999, MacData, "s15 gate Mux4.0 Mux4.1 Mux4.2 Mux4.3 Mux4.19\r");
	StrCatCk(9999, MacData,
			 "Out gate s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s12 s13 s14 s15\r");
	StrCatCk(9999, MacData, "Mux4 end\r");
	StrCatCk(9999, MacData, "Mux5 chip 37 Out\r");	/* A0 A1 A2 A3 A4 D0 ...
													   D31 */
	StrCatCk(9999, MacData, "n0  gate Mux5.0\r");
	StrCatCk(9999, MacData, "n1  gate Mux5.1\r");
	StrCatCk(9999, MacData, "n2  gate Mux5.2\r");
	StrCatCk(9999, MacData, "n3  gate Mux5.3\r");
	StrCatCk(9999, MacData, "n4  gate Mux5.4\r");
	StrCatCk(9999, MacData, "s0  gate n0 n1 n2 n3 n4 Mux5.5\r");
	StrCatCk(9999, MacData, "s1  gate Mux5.0 n1 n2 n3 n4 Mux5.6\r");
	StrCatCk(9999, MacData, "s2  gate n0 Mux5.1 n2 n3 n4 Mux5.7\r");
	StrCatCk(9999, MacData, "s3  gate Mux5.0 Mux5.1 n2 n3 n4 Mux5.8\r");
	StrCatCk(9999, MacData, "s4  gate n0 n1 Mux5.2 n3 n4 Mux5.9\r");
	StrCatCk(9999, MacData, "s5  gate Mux5.0 n1 Mux5.2 n3 n4 Mux5.10\r");
	StrCatCk(9999, MacData, "s6  gate n0 Mux5.1 Mux5.2 n3 n4 Mux5.11\r");
	StrCatCk(9999, MacData, "s7  gate Mux5.0 Mux5.1 Mux5.2 n3 n4 Mux5.12\r");
	StrCatCk(9999, MacData, "s8  gate n0 n1 n2 Mux5.3 n4 Mux5.13\r");
	StrCatCk(9999, MacData, "s9  gate Mux5.0 n1 n2 Mux5.3 n4 Mux5.14\r");
	StrCatCk(9999, MacData, "s10 gate n0 Mux5.1 n2 Mux5.3 n4 Mux5.15\r");
	StrCatCk(9999, MacData, "s11 gate Mux5.0 Mux5.1 n2 Mux5.3 n4 Mux5.16\r");
	StrCatCk(9999, MacData, "s12 gate n0 n1 Mux5.2 Mux5.3 n4 Mux5.17\r");
	StrCatCk(9999, MacData, "s13 gate Mux5.0 n1 Mux5.2 Mux5.3 n4 Mux5.18\r");
	StrCatCk(9999, MacData, "s14 gate n0 Mux5.1 Mux5.2 Mux5.3 n4 Mux5.19\r");
	StrCatCk(9999, MacData,
			 "s15 gate Mux5.0 Mux5.1 Mux5.2 Mux5.3 n4 Mux5.20\r");
	StrCatCk(9999, MacData, "s16 gate n0 n1 n2 n3 Mux5.4 Mux5.21\r");
	StrCatCk(9999, MacData, "s17 gate Mux5.0 n1 n2 n3 Mux5.4 Mux5.22\r");
	StrCatCk(9999, MacData, "s18 gate n0 Mux5.1 n2 n3 Mux5.4 Mux5.23\r");
	StrCatCk(9999, MacData, "s19 gate Mux5.0 Mux5.1 n2 n3 Mux5.4 Mux5.24\r");
	StrCatCk(9999, MacData, "s20 gate n0 n1 Mux5.2 n3 Mux5.4 Mux5.25\r");
	StrCatCk(9999, MacData, "s21 gate Mux5.0 n1 Mux5.2 n3 Mux5.4 Mux5.26\r");
	StrCatCk(9999, MacData, "s22 gate n0 Mux5.1 Mux5.2 n3 Mux5.4 Mux5.27\r");
	StrCatCk(9999, MacData,
			 "s23 gate Mux5.0 Mux5.1 Mux5.2 n3 Mux5.4 Mux5.28\r");
	StrCatCk(9999, MacData, "s24 gate n0 n1 n2 Mux5.3 Mux5.4 Mux5.29\r");
	StrCatCk(9999, MacData, "s25 gate Mux5.0 n1 n2 Mux5.3 Mux5.4 Mux5.30\r");
	StrCatCk(9999, MacData, "s26 gate n0 Mux5.1 n2 Mux5.3 Mux5.4 Mux5.31\r");
	StrCatCk(9999, MacData,
			 "s27 gate Mux5.0 Mux5.1 n2 Mux5.3 Mux5.4 Mux5.32\r");
	StrCatCk(9999, MacData, "s28 gate n0 n1 Mux5.2 Mux5.3 Mux5.4 Mux5.33\r");
	StrCatCk(9999, MacData,
			 "s29 gate Mux5.0 n1 Mux5.2 Mux5.3 Mux5.4 Mux5.34\r");
	StrCatCk(9999, MacData,
			 "s30 gate n0 Mux5.1 Mux5.2 Mux5.3 Mux5.4 Mux5.35\r");
	StrCatCk(9999, MacData,
			 "s31 gate Mux5.0 Mux5.1 Mux5.2 Mux5.3 Mux5.4 Mux5.36\r");
	StrCatCk(9999, MacData,
			 "Out gate s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s12 s13 s14 s15 s16 s17 s18 s19 s20 s21 s22 s23 s24 s25 s26 s27 s28 s29 s30 s31\r");
	StrCatCk(9999, MacData, "Mux5 end\r");
	StrCatCk(9999, MacData, "Decode chip 6 O0 O1 O2 O3 O4 O5 O6 O7\r");
	StrCatCk(9999, MacData, "n0  gate Decode.0\r");	/* A0 A1 A2 E0 E1 E2 */
	StrCatCk(9999, MacData, "n1  gate Decode.1\r");
	StrCatCk(9999, MacData, "n2  gate Decode.2\r");
	StrCatCk(9999, MacData, "O0  gate n0 n1 n2 Decode.3 Decode.4 Decode.5\r");
	StrCatCk(9999, MacData,
			 "O1  gate Decode.0 n1 n2 Decode.3 Decode.4 Decode.5\r");
	StrCatCk(9999, MacData,
			 "O2  gate n0 Decode.1 n2 Decode.3 Decode.4 Decode.5\r");
	StrCatCk(9999, MacData,
			 "O3  gate Decode.0 Decode.1 n2 Decode.3 Decode.4 Decode.5\r");
	StrCatCk(9999, MacData,
			 "O4  gate n0 n1 Decode.2 Decode.3 Decode.4 Decode.5\r");
	StrCatCk(9999, MacData,
			 "O5  gate Decode.0 n1 Decode.2 Decode.3 Decode.4 Decode.5\r");
	StrCatCk(9999, MacData,
			 "O6  gate n0 Decode.1 Decode.2 Decode.3 Decode.4 Decode.5\r");
	StrCatCk(9999, MacData,
			 "O7  gate Decode.0 Decode.1 Decode.2 Decode.3 Decode.4 Decode.5\r");
	StrCatCk(9999, MacData, "Decode end\r");
#endif
	DataIn(MacData, strlen(MacData));
	RenumMacro = FindSym("Renum");
	if (DEBUGGING > 1)
	{
		if (AllMacros == 0)
			PanicDump();
		LogIt("~InitMacros");
		LogIt("");
		LogOut();
	}
}								/* end InitMacros */

void PanicDump(void)
{								/* debugging tools.. */
	MidString aLine;
	int ix, xl, nx;
	if (DEBUGGING > 4)
	{
		LogIt("");
		LogIt("==StringTable:");
		StrZap(aLine.s);
		for (ix = 0; ix < NextStr;)
		{
			if (StringTable.s[ix] > '\0')
			{
				xl = strlen(aLine.s);
				if (xl > 50)
					xl = 75;
				else if (xl > 25)
					xl = 50;
				else if (xl > 0)
					xl = 25;
				if (xl + strlen(&StringTable.s[ix]) > 70)
				{
					LogIt(aLine.s);
					StrZap(aLine.s);
					xl = 0;
				}
				if (xl > 0)
				{
					StrCatCk(999, aLine.s, "                          ");
					SubStrCpy(aLine.s, aLine.s, 0, xl + 1);
				}
				else
					StrCpyCk(999, aLine.s, " ");
				StrCatCk(999, aLine.s, StrOf(ix));
				StrCatCk(999, aLine.s, " ");
				xl = strlen(aLine.s);
				StrCatCk(999, aLine.s, &StringTable.s[ix]);
				ix = ix + strlen(aLine.s) - xl;
			}
			else
				ix++;
		}
		if (strlen(aLine.s) > 0)
			LogIt(aLine.s);
	}
	LogIt("");
	LogIt("==Symbols:");
	xl = NextSym - NextSym / 2;
	for (ix = 0; ix < xl;)
	{
		nx = ix;
		StrCpyCk(999, aLine.s, " ");
		StrCatCk(999, aLine.s, StrOf(ix));
		StrCatCk(999, aLine.s, ": ");
		StrCatCk(999, aLine.s, StrOf(Symbols[ix++]));
		StrCatCk(999, aLine.s, " ");
		StrCatCk(999, aLine.s, StrOf(Symbols[ix++]));
		StrCatCk(999, aLine.s, "=");
		StrCatCk(999, aLine.s, SpellSym(nx));
		StrCatCk(999, aLine.s, " ");
		StrCatCk(999, aLine.s, StrOf(Symbols[ix++]));
		StrCatCk(999, aLine.s, " ");
		StrCatCk(999, aLine.s, StrOf(Symbols[ix++]));
		if (xl + ix < NextSym)
		{
			nx = xl + ix;
			if (strlen(aLine.s) < 40)
			{
				StrCatCk(999, aLine.s,
						 "                                        ");
				SubStrCpy(aLine.s, aLine.s, 0, 40);
			}
			else
				StrCatCk(999, aLine.s, " ");
			StrCatCk(999, aLine.s, StrOf(nx));
			StrCatCk(999, aLine.s, ": ");
			StrCatCk(999, aLine.s, StrOf(Symbols[nx++]));
			StrCatCk(999, aLine.s, " ");
			StrCatCk(999, aLine.s, StrOf(Symbols[nx++]));
			StrCatCk(999, aLine.s, "=");
			StrCatCk(999, aLine.s, SpellSym(xl + ix));
			StrCatCk(999, aLine.s, " ");
			StrCatCk(999, aLine.s, StrOf(Symbols[nx++]));
			StrCatCk(999, aLine.s, " ");
			StrCatCk(999, aLine.s, StrOf(Symbols[nx++]));
		}
		LogIt(aLine.s);
	}
	LogIt("");
	LogIt("==NetIndex:");
	StrZap(aLine.s);
	for (ix = 0; ix < NextNetx; ix++)
	{
		if (strlen(aLine.s) == 0)
		{
			StrCpyCk(999, aLine.s, " ");
			StrCatCk(999, aLine.s, StrOf(ix));
			StrCatCk(999, aLine.s, ":");
		}
		StrCatCk(999, aLine.s, " ");
		StrCatCk(999, aLine.s, StrOf(NetIndex[ix]));
		if (NetIndex[ix] == -1)
		{
			LogIt(aLine.s);
			StrZap(aLine.s);
		}
	}
	if (strlen(aLine.s) > 0)
		LogIt(aLine.s);
	StrCpyCk(999, aLine.s, " ");
	StrCatCk(999, aLine.s, StrOf(ix));
	StrCatCk(999, aLine.s, ":");
	LogIt(aLine.s);
	if (DEBUGGING > 7)
	{
		LogIt("");
		LogIt("==HashTable:");
		StrZap(aLine.s);
		for (ix = 0; ix < (1 << HashSize); ix++)
		{
			if (HashTable[ix] > 0)
			{
				StrCatCk(999, aLine.s, " ");
				StrCatCk(999, aLine.s, StrOf(ix));
				StrCatCk(999, aLine.s, ": ");
				StrCatCk(999, aLine.s, StrOf(HashTable[ix]));
				StrCatCk(999, aLine.s, " ");
			}
			else
				StrCatCk(999, aLine.s, ".");
			if (strlen(aLine.s) > 60)
			{
				if (StrOffs(aLine.s, ":") > 0)
					LogIt(aLine.s);
				StrZap(aLine.s);
			}
		}
		if (strlen(aLine.s) > 60)
			LogIt(aLine.s);
	}
	if (DEBUGGING > 6)
		if (NetInvert)
		{
			LogIt("");
			StrCpyCk(999, aLine.s, "==NetInvert:");
			for (ix = 0; ix < NetSize; ix++)
			{
				if (ix % 20 == 0)
				{
					LogIt(aLine.s);
					StrCpyCk(999, aLine.s, " ");
					StrCatCk(999, aLine.s, StrOf(ix));
					StrCatCk(999, aLine.s, ":");
				}
				if (ix % 10 == 0)
					StrCatCk(999, aLine.s, "  ");
				StrCatCk(999, aLine.s, " ");
				StrCatCk(999, aLine.s, StrOf(NetInvert[ix] & 255));
			}
			LogIt(aLine.s);
		}
	LogIt("");
	if (NetList == NULL)
		return;
	LogIt("==NetList:");
	xl = NetBase;
	StrZap(aLine.s);
	for (ix = 0; ix < NetAt;)
	{
		if (strlen(aLine.s) == 0)
		{
			StrCpyCk(999, aLine.s, " ");
			StrCatCk(999, aLine.s, StrOf(ix));
			if (NetInvert)
				if (ix >= NetBase)
				{
					nx = NetInvert[ix] & 255;
					if (ix >= NetStart)
						nx = nx +
							((((NetInvert[ix + 2] & 255) << 8) +
							  (NetInvert[ix + 1] & 255)) << 8);
					if (nx > 255)
					{
						StrCatCk(999, aLine.s, "'");
						StrCatCk(999, aLine.s, StrOf(nx & -256));
					}
					StrCatCk(999, aLine.s, "`");
					StrCatCk(999, aLine.s, StrOf(nx & 255));
					if (nx > 0)
					{
						StrCatCk(999, aLine.s, "/");
						StrCatCk(999, aLine.s, SpellSym(nx));
					}
				}
			StrCatCk(999, aLine.s, ":");
		}
		StrCatCk(999, aLine.s, " ");
		StrCatCk(999, aLine.s, StrOf(NetList[ix++]));
		if (ix == xl)
		{
			LogIt(aLine.s);
			StrZap(aLine.s);
			xl = ix + NetList[ix];
		}
	}
	if (strlen(aLine.s) > 0)
		LogIt(aLine.s);
	LogIt("");
}								/* end PanicDump */

void DumpAll(void)
{
	MidString aLine;
	int ix, xi, zx, locn, nby, datum, here, notBlank, whom, aName;
	char *who[] =
		{ " EQU", " GATE", " HEX", " CHIP", " ROM", " RAM", " DATA", " MBIT" };
	int skip[] = { 0, 1, 1, 4, 4, 4, 999, 9 };
	if (DEBUGGING > 1)
	{
		if (DEBUGGING > 5)
			PanicDump();
		else
			LogIt("");
		LogIt("NetIndex::");
		here = 0;
		while (here < NextNetx)
		{
			whom = NetIndex[here++];
			if (whom < 0)
				continue;
			aName = NetIndex[here++];
			if (DEBUGGING > 2)
				zx = DEBUGGING;
			else
				zx = aName;
			if (zx > 0)
			{
				LogOut();
				LogIt(" ");
				LogNum(here - 2);
				LogMo(who[whom]);
			}
			if (whom > 7)
				break;
			if (aName < 0)
			{
				if (zx > 0)
					LogMo("-");
				aName = -aName;
			}
			else if (whom == 1 || whom == 7)
			{
				LogMo(" <");
				LogNum(Symbols[aName + GateNo]);
				LogMo(">");
			}
			if (zx > 0)
			{
				LogMo(" ");
				LogMo(SpellSym(aName));
			}
			nby = skip[whom];
			while (true)
			{
				ix = NetIndex[here++];
				if (ix == -1)
					break;
				if (zx < 0)
					continue;
				LogMo(" ");
				nby--;
				if (nby < 0 && (ix & 3) == 0)
				{
					if (ix < 0)
					{
						LogMo("-");
						ix = -ix;
					}
					LogMo(SpellSym(ix));
				}
				else
					LogNum(ix);
			}
		}
		LogOut();
	}
	LogIt("");
	LogIt("Nodes:");
	for (locn = NetBase; locn < NetSize;)
	{
		here = NetInvert[locn] & 255;
		if (locn >= NetStart)
			here =
				here +
				((((NetInvert[locn + 2] & 255) << 8) +
				  (NetInvert[locn + 1] & 255)) << 8);
		StrCpyCk(999, aLine.s, "  ");
		StrCatCk(999, aLine.s, StrOf(locn));
		StrCatCk(999, aLine.s, " ");
		StrCatCk(999, aLine.s, SpellSym(here));
		StrCatCk(999, aLine.s, ":");
		ix = NetList[locn++];
		if (ix > 222 || ix <= 0 || strlen(aLine.s) > 888 || here == 0)
		{
			LogIt(aLine.s);
			SayError("Oops, NetList: ");
			LogNum(ix);
			LogMo("@");
			LogNum(locn - 1);
			LogMo(" =");
			LogNum(here);
			LogOut();
			if (ix > 222 || ix <= 0 || strlen(aLine.s) > 888)
				break;
		}
		while (--ix > 0)
		{
			StrCatCk(999, aLine.s, " ");
			StrCatCk(999, aLine.s, StrOf(NetList[locn++]));
		}
		LogIt(aLine.s);
		LogOut();
	}
	StrZap(aLine.s);
	whom = MemList;
	LogIt("");
	LogIt("Memories: ");
	LogNum(Memory[0]);
	while (whom > 0)
	{
		/* Memory: #,addr,wait,dly,loc0,#locs,#data,#addr,inputs(a,w,d) */
		/* NetIndex: 4/5,name,link,MemAt,#data,#addr,Abits(BE)[,wr,Dbits(LE)] */
		here = NetIndex[whom + 3];
		aName = NetIndex[whom + 1];
		whom = NetIndex[whom + 2];
		StrCpyCk(999, aLine.s, " ");
		StrCatCk(999, aLine.s, StrOf(here));
		StrCatCk(999, aLine.s, ": ");
		StrCatCk(999, aLine.s, SpellSym(aName));
		StrCatCk(999, aLine.s, " ");
		if (here >= Memory[0])
			break;
		ix = Memory[here++];	/* size of info */
		if (ix == 0)
			break;
		locn = Memory[here + 3];	/* loc0, location of data */
		nby = Memory[here + 4];	/* #locs, number of data words */
		datum = here + 6;		/* named inputs after this */
		while (--ix > 0)
		{
			StrCatCk(999, aLine.s, " ");
			StrCatCk(999, aLine.s, StrOf(Memory[here]));
			if (here > datum)
			{
				xi = Memory[here];
				datum = NetInvert[xi] & 255;
				if (xi >= NetStart)
				{
					zx = ((NetInvert[xi + 2] & 255) << 16);
					xi = ((NetInvert[xi + 1] & 255) << 8);
					datum = datum + xi + zx;
				}
				StrCatCk(999, aLine.s, ":");
				StrCatCk(999, aLine.s, SpellSym(datum));
				datum = 0;
			}
			here = here + 1;
		}
		notBlank = true;
		for (ix = 0; ix < nby; ix++)
		{						/* display the data.. */
			if ((ix & 15) == 0)
			{
				if (notBlank)
				{
					LogIt(aLine.s);
					LogOut();
				}
				StrCpyCk(999, aLine.s, "   ");
				StrCatCk(999, aLine.s, StrOf(ix));
				StrCatCk(999, aLine.s, ": ");
				notBlank = false;
			}
			datum = Memory[locn++];
			if (datum != UndefinedMem)
			{
				notBlank = true;
				StrCatCk(999, aLine.s, " ");
				StrCatCk(999, aLine.s, StrOf(datum));
			}
			else
				StrCatCk(999, aLine.s, " X");
		}
		LogIt(aLine.s);
		LogOut();
		StrZap(aLine.s);
	}
	LogIt(aLine.s);
	LogIt("~~~~~~~~");
	LogIt("");
	LogIt(Headers.s);
	LogOut();
	newHeads = 0;
}								/* end DumpAll */

void RunIt(void)
{								/* this actually runs the simulator.. */
	MidString aLine;
	int ix, datum, abit, here, next, wr, addr, lino, node;
	StrZap(aLine.s);
	DEBUGGING = RunDebug;
	RunTo = doClox;
	if (Trate > ClockRate || Trate < 0)
		RunTo = RunTo * ClockRate * 2;
	while (0 < RunTo--)
	{
		if (DEBUGGING > 0)
		{
			LogIt("* ");
			LogNum(Cycle);
			LogMo(" Ru2=");
			LogNum(RunTo);
			LogMo(" NxC=");
			LogNum(NextClock);
			LogMo(" PoD=");
			LogNum(PonDelay);
			LogMo(" TraPh=");
			LogNum(TraPh);
			LogOut();
		}
		if (NextClock == 0)
		{
			NextClock = ClockRate;
			ix = NetList[3];
			NetList[3] = 1 - ix;
			NetList[5] = ix;
			if (Trate > ClockRate || Trate < 0)
				if (ix == 0)
					Cycle++;
		}
		if (PonDelay > 0)
			if (--PonDelay == 0)
				NetList[7] = 1;
		Glitch = Glitch - 1;
		NetList[9] = Glitch < 4;
		NextClock--;
		TraPh--;
		node = NetStart;		/* ------------------------- do the gates.. */
		while (node < NetSize)
		{
			next = NetList[node];
			if (next == 0)
				break;
			NetList[node + 1] = NetList[node + 2];
			here = -NetList[node + 3];
			datum = 0;
			if (here > 1)
			{
				if (Memory[here + 2] <= 0)
				{
					datum = Memory[Memory[here + 1] + Memory[here + 4]];
					if (datum == UndefinedMem)
						datum = -1;
					else
						datum = (datum >> NetList[node + 4]) & 1;
				}
				else
					datum = -1;
			}
			else
				for (ix = 3; ix < next; ix++)
				{				/* gate, look at inputs.. */
					abit = NetList[node + ix];
					if (abit >= node)
						abit = NetList[abit + 2];
					else if (abit >= NetBase)
						abit = NetList[abit + 1];
					if (abit == 0)
						datum = 1;
					else if (abit < 0)
						if (datum == 0)
							datum = -1;
				}
			NetList[node + 2] = datum;
			if (DEBUGGING > 2)
				if (NetSize < 2000 || DEBUGGING > 4 || DEBUGGING > 3
					&& NetSize < 30000)
				{
					LogIt(" ~ ");
					LogNum(node);
					LogMo("=");
					LogNum(datum);
					LogOut();
				}
			node = node + next;
		}						/* end while (NetList) */
		next = 0;
		node = 2;
		while (true)
		{						/* ---------------------------------------- do 
								   the memory.. */
			/* Memory: #,addr,wait,dly,loc0,#locs,#data,#addr,inputs(a,w,d) */
			/* (mem) NetIndex:
			   4/5,name,link,MemAt,#data,#addr,Abits(BE)[,wr,Dbits(LE)] */
			if (node >= Memory[0])
				break;
			next = Memory[node];	/* size of info */
			if (next == 0)
				break;
			addr = 0;
			here = node + 8;	/* 1st address (BE'n) */
			abit = Memory[node + 7];	/* # addr bits */
			wr = Memory[here + abit];	/* write signal */
			if (wr >= NetStart)
				wr = NetList[wr + 1] | NetList[wr + 2];	/* =0 only if stable */
			else if (wr >= NetBase)
				wr = NetList[wr + 1];
			for (ix = abit; ix > 0; ix--)
			{					/* address is BE'n */
				lino = Memory[here++];	/* look at address inputs.. */
				abit = lino;
				if (lino >= NetBase)
				{
					abit = NetList[lino + 1];
					if (lino >= NetStart)
						if (abit != NetList[lino + 2])
							abit = -1;
				}
				if (abit < 0)
				{
					addr = -1;
					break;
				}
				addr = addr * 2 + abit;
			}
			if (addr < 0)
				addr = rand() & (Memory[node + 5] - 1);
			datum = 0;
			here = node + next;
			for (ix = Memory[node + 6]; ix > 0; ix--)
			{					/* data is LE'n, calc'd BE'n.. */
				lino = Memory[--here];	/* look at data inputs.. */
				abit = lino;
				if (lino >= NetBase)
				{
					abit = NetList[lino + 1];
					if (lino >= NetStart)
						if (abit != NetList[lino + 2])
							abit = -1;
				}
				if (abit < 0)
				{
					datum = -1;
					break;
				}
				datum = datum * 2 + abit;
			}
			here = Memory[node + 4];
			abit = Memory[node + 3];
			lino = Memory[node + 1];
			if (lino != addr)
			{					/* address changed, restart delay */
				if (wr == 0)
				{				/* active write trashes both.. */
					if (lino >= 0)
						Memory[here + lino] = UndefinedMem;
					Memory[here + addr] = UndefinedMem;
					ix = Memory[node - 1];
					/* if (DEBUGGING!=0) */ if (ix > 0)
					{
						StrCpyCk(999, aLine.s, "--- ");
						StrCatCk(999, aLine.s, SpellSym(Memory[node]));
						StrCatCk(999, aLine.s, "[");
						if (lino >= 0)
						{
							StrCatCk(999, aLine.s, StrOf(lino));
							StrCatCk(999, aLine.s, "/");
						}
						LogIt(aLine.s);
						LogNum(addr);
						LogMo("] = ??");
						LogOut();
					}
				}
				Memory[node + 2] = abit;
				Memory[node + 1] = addr;
			}
			else if (0 >= Memory[node + 2]--)
				if (wr == 0)
				{				/* write active.. */
					if (datum == UndefinedMem)
						Redefine();
					Memory[here + addr] = datum;
					Memory[node + 2] = abit;
					ix = Memory[node - 1];
					if (ix > 0)
					{
						LogIt("--- ");
						LogMo(SpellSym(Memory[node - 1]));
						LogMo("[");
						LogNum(addr);
						LogMo("] = ");
						LogNum(datum);
						if ((datum > 31) || (datum + 31 < 0))
						{
							StrZap(aLine.s);
							ix = datum;
							if (datum < 0)
								if (datum + 0x10000000 > 0)
									ix = -ix;
							while (ix > 0)
							{
								abit = ix & 15;
								if (abit > 9)
									abit = abit + 7;
								zWord.s[0] = (char)(abit + 48);
								zWord.s[1] = '\0';
								StrCatCk(99, zWord.s, aLine.s);
								StrCpyCk(99, aLine.s, zWord.s);
								ix = (ix >> 4) & 0xFFFFFFF;
							}
							LogMo(" = ");
							if (datum < 0)
								LogMo("-");
							LogMo("0x");
							LogMo(aLine.s);
						}
						LogOut();
					}
				}
			if (DEBUGGING > 1)
			{
				LogIt(" %");
				LogNum(node);
				LogMo(": ");
				LogNum(here);
				LogMo("~");
				LogNum(lino);
				LogMo("/");
				LogMo(SpellSym(Memory[node]));
				LogMo("[");
				LogNum(addr);
				LogMo("]=");
				LogNum(datum);
				LogIt(" !");
				LogNum(wr);
				LogMo(" ^");
				LogNum(Memory[node + 2]);
				LogOut();
			}
			node = node + next + 1;
		}						/* end while (Memory) */
		if (TraPh <= 0)
		{						/* ------------------------------ time for a
								   trace line.. */
			if (Trate < 0)
			{					/* only if this signal is true.. */
				abit = -Trate;
				if (abit >= NetStart)
					abit++;
				if (abit >= NetBase)
					abit = NetList[abit + 1];
				if (abit <= 0)
					continue;
				if (Glitch > 0)
					continue;
			}
			else
				TraPh = TraPh + Trate;
			StrZap(aLine.s);
			next = 0;
			datum = 32;
			while (TraceSize > next)
			{
				abit = TraceList[next++];
				if (abit < 0)
				{				/* space.. */
					StrCatCk(999, aLine.s, " ");
					datum = 32;
					continue;
				}
				if (abit >= NetStart)
					abit++;
				if (abit >= NetBase)
					abit = NetList[abit + 1] & 17;
				datum = datum * 2 + abit;
				if (datum > 511)
				{
					if (datum < 528)
					{
						datum = (datum & 15) + 48;
						if (datum > 57)
							datum = datum + 7;
						StrCpyCk(9, zWord.s, ".");
						zWord.s[0] = (char)datum;
						StrCatCk(999, aLine.s, zWord.s);
					}
					else
						StrCatCk(999, aLine.s, "X");
					datum = 32;
				}
			}					/* end while (TraceList) */
			LogIt(aLine.s);
			LogMo(" ");
			LogNum(Cycle);
			LogOut();
			if (Glitch <= 0)
				Glitch = 7;
			newHeads++;
			if (newHeads > 40)
			{
				newHeads = 0;
				LogIt("");
				LogIt(Headers.s);
			}
			if (Trate > 0)
				if (Trate <= ClockRate)
					Cycle++;
		}
	}							/* end while (RunTo) */
	LogIt("");
	LogOut();
	if (DEBUGGING > 0)
		DumpAll();
}								/* end RunIt */

void Redefine(void)
{								/* find an unused memory value for
								   UndefinedMem */
	int tryit, here, ix;
	for (ix = 0; ix < 33; ix++)
	{							/* try a few random numbers.. */
		tryit = rand();
		if (tryit == 0)
			continue;
		if (tryit == UndefinedMem)
			continue;
		for (here = DataAt; here < MemSize; here++)
			if (Memory[here] == tryit)
			{
				tryit = 0;
				break;
			}
		if (tryit != 0)
		{
			for (here = DataAt; here < MemSize; here++)
				if (Memory[here] == UndefinedMem)
					Memory[here] = tryit;
			UndefinedMem = tryit;
			return;
		}
	}
	LogIt("---- Looking for a new X");
	LogOut();
	for (tryit = (rand() << 12) + 1;; tryit++)
	{
		if (tryit == UndefinedMem)
			continue;
		if ((tryit & 4095) == 0)
		{
			LogIt("     Still looking..");
			LogOut();
		}
		if (tryit == 0)
			continue;
		for (here = DataAt; here < MemSize; here++)
			if (Memory[here] == tryit)
			{
				tryit = 0;
				break;
			}
		if (tryit != 0)
		{
			for (here = DataAt; here < MemSize; here++)
				if (Memory[here] == UndefinedMem)
					Memory[here] = tryit;
			UndefinedMem = tryit;
			return;
		}
	}
}								/* end Redefine */

void LogOut(void)
{								/* output trace log to both screen and file.. */
	int ix;
	char *stp = OutData;
	for (ix = strlen(OutData); ix > 0; ix--)
		if (*stp != '\r')
			putchar(*stp++);
		else
			stp++;
	stp = OutData;
	if (TheLogFile)
	{
		for (ix = strlen(OutData); ix > 0; ix--)
		{
			if (*stp == '\n' && CRonly)
				stp++;
			else
				putc(*stp++, TheLogFile);
		}
		fflush(TheLogFile);
	}
	StrZap(OutData);
}								/* end console version of LogOut */

/*********************************************************
ToDo...
Needed part types:
  Schmidt Trigger: forces a 0/1 output from X input
  Input: text chars from file
  Output: text chars to file
  Event: stochastic delay
  Show: like HEX, but for interactive display
  Trace Options: if/else, inserted chars, tabs
  Quiet RAM option (no write trace)
  FF macro that doesn't oscillate
Other enhancements:
  Interactive display, with panels for live regs, memory, ...
**********************************************************/
