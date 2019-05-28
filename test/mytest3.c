#include "seahorn/seahorn.h"

extern int unknown1();
extern int unknown2();


int main()
{
	unsigned int a = 7;

	while(unknown1()){
		a++;
	}
	sassert(a>0);

}
