#include "seahorn/seahorn.h"

extern int unknown1();
extern int unknown2();


int main()
{
	int a;
	a++;
	sassert(a>3);

}
