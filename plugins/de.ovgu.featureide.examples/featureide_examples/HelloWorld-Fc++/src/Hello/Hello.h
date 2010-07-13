//File Hello/Hello.h
#include <stdio.h>
class Hello {
public:
	int run() { 
		printf("Hello");
		return 0;
	}
};

int main() {

	//create instance of "test"
	Hello myHello;

	//run Hello::run as entry-point of the app
	return myHello.run();
}
