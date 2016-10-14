//File Wonderful/Main.h
refines class Main {
public:
	int run() { 
		int res = super::run(); 
		if (res!=0)
			return res;

		printf(" wonderful");
		return 0;
	}
};
