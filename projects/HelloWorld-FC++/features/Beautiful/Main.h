//File Beautiful/Main.h
refines class Main {
public:
	int run() { 
		int res = super::run(); 
		if (res!=0)
			return res;

		printf(" beautiful");
		return 0;
	}
};
