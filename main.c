/* GateSim main program -- 2003 July 24 */

#include <stdio.h>
#include <stdlib.h>
#include <string.h>

void MyFileDialog(char *theName, int nameLen, char *theFilter);
void ReadData(FILE * theObj, char *InData, int DataLen);
void RunIt(void);

FILE *theFile = NULL;

void ReadaFile(char *filename)
{
	int here, DataLen;
	char FileName[256];
	char iline[1000];
	char InData[100000];

	strcpy(FileName, filename);
	if (strlen(FileName) > 0)
	{
		theFile = fopen(FileName, "r");
		if (theFile)
		{
			fgets(InData, 999, theFile);
			DataLen = strlen(InData);
			while (!feof(theFile))
			{
				fgets(iline, 999, theFile);
				here = strlen(iline);
				if (DataLen + here + 1 < sizeof(InData))
				{
					strcat(InData, "\r\n");
					strcat(InData, iline);
					DataLen = DataLen + here + 2;
				}
				else
					break;
			}
			fclose(theFile);
			theFile = NULL;
			here = strlen(FileName) - 4;
			if (here > 0)
			{
				if (strncmp(&FileName[here], ".txt", 4))
				{
					strncpy(&FileName[here+1], "log", 3);
					theFile = fopen(FileName, "r+b");
				}
				ReadData(theFile, InData, DataLen);
			}
		}
	}
}

int main(int argc, char **argv)
{
	if(argc <= 1)
	{
		printf("Usage: %s <GateCode file>\n", argv[0]);
		return 0;
	}
	ReadaFile(argv[1]);
	do
	{
		RunIt();
	}
	while (getchar());
	if (theFile)
		fclose(theFile);
	return 0;
}
