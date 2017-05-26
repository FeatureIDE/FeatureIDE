#include <stdio.h>
#include <stdlib.h>

int main(void) {
	printf("Hello");
#ifdef Beautiful
	printf(" beautiful");
#endif
#ifdef Wonderful
	printf(" wonderful");
#endif
#ifdef World
	printf(" world");
#endif
	return 0;
}
