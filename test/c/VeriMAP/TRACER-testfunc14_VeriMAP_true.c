extern void __VERIFIER_error() __attribute__((noreturn));
void __VERIFIER_assert (int cond) { if (!cond) __VERIFIER_error (); }
unsigned int __VERIFIER_nondet_uint();
void errorFn() {ERROR: goto ERROR;}
# 1 "MAP/SAFE-exbench/TRACER-testfunc14.tmp.c"
# 1 "<command-line>"
# 1 "MAP/SAFE-exbench/TRACER-testfunc14.tmp.c"
# 23 "MAP/SAFE-exbench/TRACER-testfunc14.tmp.c"

void bar(){
  int i,NONDET,q,z;
  i=0;

  if (q>0) z=4;
  else z=5;

  while (NONDET){
    i++;
  }
  return;
}

main(){
  int p,x;

  if (p>0) x=1;
  else x=3;

  bar();

  __VERIFIER_assert(!( x==2 ));

}
