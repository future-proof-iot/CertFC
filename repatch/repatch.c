#include<stdio.h>
#include<stdint.h>
#include <inttypes.h>

int main(){
  char buffer[500];
  char newbuffer[500];
  FILE *ptr_r, *ptr_w;
  int i,f;

  ptr_r = fopen("generated.c", "r");
  ptr_w = fopen("new_generated.c", "w+");
  f = 0;
  while (1){
    char c = fgetc(ptr_r);
    if (feof(ptr_r)){
      break;
    }
    if (c == '$'){
      f = 1;
      continue;
    }
    if (f == 1 && '0' <= c && c <= '9'){
      continue;
    }
    else{
      f = 0;
    }
    fputc(c, ptr_w);
  }
  
  if (feof(ptr_r))
  {
    printf ("\n!Completing the repatch process!\n");
    fclose(ptr_r);
    fclose(ptr_w);
  }
  return 0;
}
