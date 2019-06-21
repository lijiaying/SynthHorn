#include "seahorn/seahorn.h"

int main()
{
	int a = 6;
	int b = 3;
	if (a>0 && a<20) {
		while(b>0){
			a++;
			b--;
		}
		sassert(a>0);
	}
}
