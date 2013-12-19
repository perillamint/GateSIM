#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#ifdef __POWERPC__
#define DefaultFile "Snowball:Academic:Tools:MIPS:MIPSgate.txt"
#else
#define DefaultFile "G:\\CLASS\\Computer Science\\CIS2233\\MIPSgate.txt"
#endif

// using namespace std;

#define byte char
#define false 0
#define true 1
#define NetStart  12
#define NetBase  2
#define TX  44
#define ErrMaxOff 99
#define CRonly true

#define SmallString struct Small_String
#define MidString struct Mid_String
#define HugeString struct Huge_String
// /#define BigString struct Big_String
// /#define MegaString struct Mega_String

// #define iAbs(x) ((x)<0?-(x):x)

SmallString
{
	char s[100];
};

MidString
{
	char s[1000];
};

HugeString
{
	char s[MaxStrs];
};

// /BigString {char s[10000];};
// /MegaString {char s[1200000];};

void StrZap(char *theStr);
void StrReplace(char *theStr, char oldc, char newc);
int StrOffs(char *theStr, char *aStr);
void StrCpyCk(int mx, char *deStr, char *theStr);
void StrCatCk(int mx, char *deStr, char *theStr);
void SubStrCpy(char *deStr, char *theStr, int fst, int lst);
char *SubStr(char *theStr, int fst, int lst);
void Int2Str(char *theStr, int valu);
char *Num2Str(char *theStr, int valu);
char *StrOf(int valu);
int IntOf(char *theStr);
char *SpellSym(int sym);		// just returns string offs ptr
int FindSym(char *name);		// hashes name, looks it up or adds it
void Pacify(int doWhat, char *theMsg);
void LogMo(char *theMsg);
void LogNum(int theNum);
void LogIt(char *theMsg);
void ReadData(GateObjFi * theObj, char *InData, int DataLen);
void DataIn(char *InData, int DataLen);
void BuildNet(void);
int FindNode(int theRef, char *whom);
void SayError(char *theMsg);
void CheckOflo(int is, int mx, char *sayso);
int WordCount(char *theStr);
char *GetWord(int wdno, char *theStr);
int Numify(char *theStr, int nbits);
void InitMacros(void);
void PanicDump(void);
void DumpAll(void);
void RunIt(void);
void Redefine(void);
void LogOut(void);

