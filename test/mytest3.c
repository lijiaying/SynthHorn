#include "seahorn/seahorn.h"

extern int unknown1();
extern int unknown2();


int main()
{
	int a = unknown1();

	if (a>0) {
		while(unknown2()){
			a++;
		}
		sassert(a>0);
	}

}
