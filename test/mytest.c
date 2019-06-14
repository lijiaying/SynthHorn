#include "seahorn/seahorn.h"

extern int unknown1();
extern int unknown2();


int main()
{
	int a = unknown1();
	int b = unknown2();
	if (a>0 && a<200 && b<20) {
		while(b>0){
			a++;
			b--;
		}
		sassert(a>0);
	}
}
