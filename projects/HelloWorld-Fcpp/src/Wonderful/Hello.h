//File Wonderful/Hello.h
refines class Hello {
public:
	int run() { 
		int res = super::run(); 
		if (res!=0)
			return res;

		printf(" wonderful");
		return 0;
	}
};
