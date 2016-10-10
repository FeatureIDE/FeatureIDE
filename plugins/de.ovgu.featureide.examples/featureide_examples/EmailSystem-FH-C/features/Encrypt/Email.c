void
printMail (struct email *msg)
{
  original (msg);
  printf ("ENCRYPTED\n  %i\n", msg->isEncrypted);
  printf ("ENCRYPTION KEY\n  %s\n", msg->encryptionKey);
}

struct email *
cloneEmail (struct email *msg)
{
  struct email *clone = original (msg);
  clone->isEncrypted = msg->isEncrypted;
  if (msg->encryptionKey)
    clone->encryptionKey = strdup (msg->encryptionKey);
  return clone;
}

int
isEncrypted (struct email *msg)
{
  return msg->isEncrypted;
}

int
isReadable (struct email *msg)
{
  if (0 == isEncrypted (msg))
    return original (msg);
  else
    return 0;
}
