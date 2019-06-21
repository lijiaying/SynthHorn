#include "seahorn/seahorn.h"

extern int unknown1();
extern int unknown2();


int main()
{
	int a;
	int b;
	if (a+b>0) {
		while(unknown1()){
			a++;
			b--;
		}
		sassert(a+b>0);
	}
}
