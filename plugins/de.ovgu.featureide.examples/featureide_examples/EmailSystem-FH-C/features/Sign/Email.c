void
printMail (struct email *msg)
{
  original (msg);
  printf ("SIGNED\n  %i\n", msg->isSigned);
  printf ("SIGNATURE\n  %s\n", msg->signKey);
}

struct email *
cloneEmail (struct email *msg)
{
  struct email *clone = original (msg);
  clone->isSigned = msg->isSigned;
  if (msg->signKey)
    clone->signKey = strdup (msg->signKey);
  return clone;
}

int
isSigned (struct email *msg)
{
  return msg->isSigned;
}
