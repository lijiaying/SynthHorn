#include "seahorn/seahorn.h"

extern int unknown1();
extern int unknown2();
extern int unknown3();


int main()
{
	int a = unknown1();
	int b = unknown2();
	// if (a>0 && a<200 && b<20) {
	if (a+b>0) {
		while(unknown3()){
			a++;
			b--;
		}
		sassert(a+b>0);
	}
}
