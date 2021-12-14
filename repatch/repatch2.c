/**
 * 1. deleting all lines before `unsigned long long list_get`
 * 2. deleting `\n\n`.
 * 2. deleting all `extern` lines
 * 3. adding `st` to all possible places
 */

#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#define BUFFER_SIZE 1000
#define CNT 1000

/* Function declaration */
void replaceAll(char *str, const char *oldWord, const char *newWord);


const char start_point[] = "unsigned long long list_get";


const char old_words[][100] = {
	"eval_pc()",
	"upd_pc(pc",
	"upd_pc_incr()",
	"upd_reg(dst",
	"eval_reg(dst",
	"eval_reg(src",
	"upd_flag(0)", 
	"upd_flag(-", 
	"upd_flag(1",
	"eval_flag()",
	"check_mem(1U",
	"check_mem(2U",
	"upd_reg(1U",
	
	"eval_mem_regions()",
	"void step_opcode_alu64(",
	"step_opcode_alu64(dst64",
	"void step_opcode_alu32(",
	"step_opcode_alu32(dst32",
	"void step_opcode_branch(",
	"step_opcode_branch(dst64",
	"void step_opcode_mem_ld_imm(",
	"step_opcode_mem_ld_imm(imm",
	"void step_opcode_mem_ld_reg(",
	
	"step_opcode_mem_ld_reg(addr",
	"void step_opcode_mem_st_imm(",
	"step_opcode_mem_st_imm(imm",
	"void step_opcode_mem_st_reg(",
	"step_opcode_mem_st_reg(src",
	"load_mem(1",
	"load_mem(2",
	"load_mem(4",
	"load_mem(8",
	"store_mem_imm(1",
	"store_mem_imm(2",
	"store_mem_imm(4",
	"store_mem_imm(8",
	"store_mem_reg(1",
	
	"store_mem_reg(2",
	"store_mem_reg(4",
	"store_mem_reg(8",
	"store_mem_reg(1",
	"store_mem_reg(2",
	"store_mem_reg(4",
	"store_mem_reg(8",
	"unsigned int check_mem_aux(",
	"return check_mem_aux(",
	"unsigned int check_mem(",
	
	"void step(",
	"step(len, l);",
	"void bpf_interpreter_aux(",
	"bpf_interpreter_aux(len",	
	"unsigned long long bpf_interpreter(",
	"struct memory_region *get_mem_region(",
	"= get_mem_region(",
	"return eval_reg(",
	"eval_mem_num()",
	"check_mem = check_mem_aux(",
	
	"unsigned long long list_get(",
	"unsigned int get_dst(",
	"unsigned int reg64_to_reg32(",
	"unsigned int get_src(",
	"int get_offset(",
	"int get_immediate(",
	"unsigned long long eval_immediate(",
	"unsigned char get_opcode_ins(",
	"unsigned char get_opcode_alu64(",
	"unsigned char get_opcode_alu32(",
	"unsigned char get_opcode_branch(",
	"unsigned char get_opcode_mem_ld_imm(",
	"unsigned char get_opcode_mem_ld_reg(",
	"unsigned char get_opcode_mem_st_imm(",
	"unsigned char get_opcode_mem_st_reg(",
	"unsigned char get_opcode(",
	"unsigned int get_add(",
	"unsigned int get_sub(",
	"unsigned int get_addr_ofs(",
	"_Bool is_well_chunk_bool(",
	"unsigned int check_mem_aux2(",
	"_Bool comp_and_0x08_byte("
	
	};

const char new_words[][100] = {
	"eval_pc(st)",
	"upd_pc(st, pc",
	"upd_pc_incr(st)",
	"upd_reg(st, dst", 
	"eval_reg(st, dst",
	"eval_reg(st, src",
	"upd_flag(st, 0)", 
	"upd_flag(st, -", 
	"upd_flag(st, 1", 
	"eval_flag(st)",
	"check_mem(st, 1U",
	"check_mem(st, 2U",
	"upd_reg(st, 1U",
	
	"eval_mem_regions(st)",
	"void step_opcode_alu64(struct bpf_state* st, ",
	"step_opcode_alu64(st, dst64",
	"void step_opcode_alu32(struct bpf_state* st, ",
	"step_opcode_alu32(st, dst32",
	"void step_opcode_branch(struct bpf_state* st, ",
	"step_opcode_branch(st, dst64",
	"void step_opcode_mem_ld_imm(struct bpf_state* st, ",
	"step_opcode_mem_ld_imm(st, imm",
	"void step_opcode_mem_ld_reg(struct bpf_state* st, ",
	
	"step_opcode_mem_ld_reg(st, addr",
	"void step_opcode_mem_st_imm(struct bpf_state* st, ",
	"step_opcode_mem_st_imm(st, imm",
	"void step_opcode_mem_st_reg(struct bpf_state* st, ",
	"step_opcode_mem_st_reg(st, src",
	"load_mem(st, 1",
	"load_mem(st, 2",
	"load_mem(st, 4",
	"load_mem(st, 8",
	"store_mem_imm(st, 1",
	"store_mem_imm(st, 2",
	"store_mem_imm(st, 4",
	"store_mem_imm(st, 8",
	"store_mem_reg(st, 1",
	
	"store_mem_reg(st, 2",
	"store_mem_reg(st, 4",
	"store_mem_reg(st, 8",
	"store_mem_reg(st, 1",
	"store_mem_reg(st, 2",
	"store_mem_reg(st, 4",
	"store_mem_reg(st, 8",
	"unsigned int check_mem_aux(struct bpf_state* st, ",
	"return check_mem_aux(st, ",
	"unsigned int check_mem(struct bpf_state* st, ",
	
	"void step(struct bpf_state* st, ",
	"step(st, len, l); //print_bpf_state(st);",
	"void bpf_interpreter_aux(struct bpf_state* st, ",
	"bpf_interpreter_aux(st, len",
	"unsigned long long bpf_interpreter(struct bpf_state* st, ",
	"static struct memory_region *get_mem_region(struct bpf_state* st, ",
	"= get_mem_region(st, ",
	"return eval_reg(st, ",
	"eval_mem_num(st)",
	"check_mem = check_mem_aux(st, ",
	
	"static unsigned long long list_get(",
	"static unsigned int get_dst(",
	"static unsigned int reg64_to_reg32(",
	"static unsigned int get_src(",	
	"static int get_offset(",
	"static int get_immediate(",
	"static unsigned long long eval_immediate(",
	"static unsigned char get_opcode_ins(",
	"static unsigned char get_opcode_alu64(",
	"static unsigned char get_opcode_alu32(",
	"static unsigned char get_opcode_branch(",
	"static unsigned char get_opcode_mem_ld_imm(",
	"static unsigned char get_opcode_mem_ld_reg(",
	"static unsigned char get_opcode_mem_st_imm(",
	"static unsigned char get_opcode_mem_st_reg(",
	"static unsigned char get_opcode(",
	"static unsigned int get_add(",
	"static unsigned int get_sub(",
	"static unsigned int get_addr_ofs(",
	"static _Bool is_well_chunk_bool(",
	"static unsigned int check_mem_aux2(",
	"static _Bool comp_and_0x08_byte("
	
	};
	


const char delete_lines[] ="extern ";

int main()
{
    /* File pointer to hold reference of input file */
    FILE * ptr_r;
    FILE * ptr_w;
    int counter = CNT;
    int index;
    int before_start_point;
    int two_blanks;
    
    char buffer[BUFFER_SIZE];



    /*  Open all required files */
    ptr_r  = fopen("repatch1_generated.c", "r");
    ptr_w = fopen("repatch2_generated.c", "w+"); 

    /* fopen() return NULL if unable to open file in given mode. */
    if (ptr_r == NULL || ptr_w == NULL)
    {
        /* Unable to open file hence exit */
        printf("\nUnable to open file.\n");
        printf("Please check whether file exists and you have read/write privilege.\n");
        exit(EXIT_SUCCESS);
    }

    before_start_point = 0;
    two_blanks = 0;
    while ((fgets(buffer, BUFFER_SIZE, ptr_r)) != NULL)
    {  //printf("%d\n", CNT-counter);
    	//if ((counter --) == 0) { break; }
    	/* deleting all lines before `unsigned long long list_get` */
    	if (before_start_point == 0 && strstr(buffer, start_point) == NULL){
    	  /* we just skip this line and don't write it */
    	  continue;
    	}
    	else {
    	  before_start_point = 1;
    	}
    	
    	if (strcmp(buffer, "\n") == 0){
    	  if(two_blanks == 0){
    	    two_blanks = 1;
    	  }
    	  else {//two_blanks == 1
    	    //printf("skip\n");
    	    continue;
    	  }
    	}
    	else if(strcmp(buffer, "}\n") == 0) {
    	  /* we just skip this line and don't write it */
    	  two_blanks = 0;
    	}
    	
    	/* Delete all lines starting by `extern  ` */
    	if (strstr(buffer, delete_lines) != NULL){
    	  /* we just skip this line and don't write it */
    	  continue;
    	}
    	
    	if(strcmp(buffer,"\n") == 0) { fputs(buffer, ptr_w); continue; }
    
    	//printf("readline: %s\n", buffer);
        // Replace all occurrence of word from current line
        for (index = 0; index < sizeof(old_words)/100; index ++){
          replaceAll(buffer, old_words[index], new_words[index]);
        }

        // After replacing write it to temp file.
        fputs(buffer, ptr_w);
    }

    //printf("repatch2 done!\n");
    /* Close all files to release resource */
    fclose(ptr_r);
    fclose(ptr_w);

    return 0;
}



/**
 * Replace all occurrences of a given a word in string.
 */
void replaceAll(char *str, const char *oldWord, const char *newWord)
{
    char *pos, temp[BUFFER_SIZE];
    int index = 0;
    int owlen;

    owlen = strlen(oldWord);

    // Fix: If oldWord and newWord are same it goes to infinite loop
    if (!strcmp(oldWord, newWord)) {
        return;
    }

    if ((pos = strstr(str, oldWord)) == NULL) {return ;}
    /*
     * Repeat till all occurrences are replaced. 
     */
    //while ((pos = strstr(str, oldWord)) != NULL)
    //{
        // Backup current line
        strcpy(temp, str);

        // Index of current found word
        index = pos - str;

        // Terminate str after word found index
        str[index] = '\0';

        // Concatenate str with new word 
        strcat(str, newWord);
        
        // Concatenate str with remaining words after 
        // oldword found index.
        strcat(str, temp + index + owlen);
    //}
}
