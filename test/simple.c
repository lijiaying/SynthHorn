#include "seahorn/seahorn.h"

extern int unknown();

int main()
{
	int a = unknown();
	int b = 3;
	if (a>0 && a<20) {
		while(b>0){
			a++;
			b--;
		}
		sassert(a>0);
	}
}
