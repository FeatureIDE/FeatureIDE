void sig_verify ( int gcry, int valid ) {

	int BAD_SIGN = 0;

	#ifdef LIBGCRYPT
	  	// Code here..
		if (gcry != BAD_SIGN) {
			set_error(2);
	#endif

	#ifdef LIBCRYPTO
		// Code here..
		if (valid == -1) {
			set_error(3);
	#endif

		// Several lines of code here..
	} //if neither LIBGCRYPT nor LIBCRYPTO is activated we will have the '}' without the opening '{'

}
