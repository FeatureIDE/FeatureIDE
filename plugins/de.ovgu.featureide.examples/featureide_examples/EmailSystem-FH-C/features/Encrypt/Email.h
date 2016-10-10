struct email
{
  int isEncrypted;
  char *encryptionKey;
};

int isEncrypted (struct email *msg);
