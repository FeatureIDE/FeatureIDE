void free (char* hex){
	// Do nothing..
}

void ssh_print_bignum(){
	#ifdef LIBGCRYPT
	  	unsigned char *hex;
	#endif

	#ifdef LIBCRYPTO
		char *hex;
	#endif

	free(hex);
}



