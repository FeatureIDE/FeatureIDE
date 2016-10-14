void
printMail (struct email *msg)
{
  original (msg);
  printf ("SIGNATURE VERIFIED\n  %i\n", msg->isSignatureVerified);
}

struct email *
cloneEmail (struct email *msg)
{
  struct email *clone = original (msg);
  clone->isSignatureVerified = msg->isSignatureVerified;
  return clone;
}

int
isVerified (struct email *msg)
{
  return msg->isSignatureVerified;
}
