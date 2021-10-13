extern unsigned long long testget(unsigned int, unsigned long long, unsigned long long, unsigned long long *);

unsigned long long testget(unsigned int fuel, unsigned long long init, unsigned long long idx, unsigned long long *l)
{
  if (fuel == 0U) {
    return init;
  } else {
    return *(l + idx);
  }
}


