#ifndef Main_h__included
#define Main_h__included

//Layer Hello


#line 1 "D:/Daten/runtime-EclipseApplication/HelloWorld-FC++/features/Hello/Main.h"
//File Hello/Main.h
#include <stdio.h>

//Layer Beautiful


#line 1 "D:/Daten/runtime-EclipseApplication/HelloWorld-FC++/features/Beautiful/Main.h"
//File Beautiful/Main.h

//Layer World


#line 1 "D:/Daten/runtime-EclipseApplication/HelloWorld-FC++/features/World/Main.h"
//File World/Main.h


#line 3 "D:/Daten/runtime-EclipseApplication/HelloWorld-FC++/features/Hello/Main.h"
class Main {
//**** Layer Hello ****
#line 3 "D:/Daten/runtime-EclipseApplication/HelloWorld-FC++/features/Hello/Main.h"

public:
	inline 
#line 5 "D:/Daten/runtime-EclipseApplication/HelloWorld-FC++/features/Hello/Main.h"
int Hello_run() { 
		printf("Hello");
		return 0;
	}

//**** Layer Beautiful ****
#line 2 "D:/Daten/runtime-EclipseApplication/HelloWorld-FC++/features/Beautiful/Main.h"

public:
	inline 
#line 4 "D:/Daten/runtime-EclipseApplication/HelloWorld-FC++/features/Beautiful/Main.h"
int Beautiful_run() { 
		int res = Hello_run(); 
		if (res!=0)
			return res;

		printf(" beautiful");
		return 0;
	}

//**** Layer World ****
#line 2 "D:/Daten/runtime-EclipseApplication/HelloWorld-FC++/features/World/Main.h"

public:
	int run() { 
		int res = Beautiful_run(); 
		if (res!=0)
			return res;

		printf(" World!");
		return 0;
	}

#line 9 "D:/Daten/runtime-EclipseApplication/HelloWorld-FC++/features/Hello/Main.h"
};
#endif //Main_h__included

