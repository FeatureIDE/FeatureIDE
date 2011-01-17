//File Hello/Main.h
#include <stdio.h>
class Main {
public:
	int run() { 
		printf("Hello");
		return 0;
	}
};

int main() {

	//create instance of "Main"
	Main myHello;

	//run Main::run as entry-point of the app
	return myHello.run();
}
