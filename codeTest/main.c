#include <stdio.h>
#include "generated.h"

static const unsigned char wrap_around_data[] =
        "AD3Awn4kb6FtcsyE0RU25U7f55Yncn3LP3oEx9Gl4qr7iDW7I8L6Pbw9jNnh0sE4DmCKuc"
        "d1J8I34vn31W924y5GMS74vUrZQc08805aj4Tf66HgL1cO94os10V2s2GDQ825yNh9Yuq3"
        "QHcA60xl31rdA7WskVtCXI7ruH1A4qaR6Uk454hm401lLmv2cGWt5KTJmr93d3JsGaRRPs"
        "4HqYi4mFGowo8fWv48IcA3N89Z99nf0A0H2R6P0uI4Tir682Of3Rk78DUB2dIGQRRpdqVT"
        "tLhgfET2gUGU65V3edSwADMqRttI9JPVz8JS37g5QZj4Ax56rU1u0m0K8YUs57UYG5645n"
        "byNy4yqxu7";

struct $107 memory_regions;

struct fletcher32_ctx {
  const unsigned short * data;
  unsigned int words;
} 

struct fletcher32_ctx f32_ctx = {
  .data = (const unsigned short *) wrap_around_data,
  .words = sizeof(wrap_around_data)/2,
};

void bpf_add_region_ctx(){
  memory_regions.$108.$105 = &f32_ctx;
  memory_regions.$108.$106 = sizeof(f32_ctx);
}

void bpf_add_region_content(){
  memory_regions.$110.$105 = (void*)wrap_around_data;
  memory_regions.$110.$106 = sizeof(wrap_around_data);
}

int main(){
  
  return 0;
}


