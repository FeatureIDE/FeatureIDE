//File World/Hello.h
refines class Hello {
public:
	int run() { 
		int res = super::run(); 
		if (res!=0)
			return res;

		printf(" World!");
		while (true);
		return 0;
	}
};
