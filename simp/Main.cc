/*****************************************************************************************[Main.cc]
Copyright (c) 2003-2006, Niklas Een, Niklas Sorensson
Copyright (c) 2007,      Niklas Sorensson

Permission is hereby granted, free of charge, to any person obtaining a copy of this software and
associated documentation files (the "Software"), to deal in the Software without restriction,
including without limitation the rights to use, copy, modify, merge, publish, distribute,
sublicense, and/or sell copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all copies or
substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR IMPLIED, INCLUDING BUT
NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND
NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM,
DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT
OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
**************************************************************************************************/

#include <errno.h>
#include <vector>

#include <algorithm>
#include <iostream>
#include <string>

#include <signal.h>
#include <zlib.h>
#include <sys/resource.h>

#include "utils/System.h"
#include "utils/ParseUtils.h"
#include "utils/Options.h"
#include "core/Dimacs.h"
#include "simp/SimpSolver.h"

#define CSIZE 4096 
#define POP_INPUT 6
#define ARCH_INPUT 28 
#define ARCH_SEL_INPUT 5 

const int list_of_6and7_input[8] = {5, 6, 12, 13, 19, 20, 26, 27};
const int list_of_lut_start[4] = {0, 7, 14, 21};

using namespace Minisat;

//=================================================================================================


void printStats(Solver& solver)
{
    double cpu_time = cpuTime();
    double mem_used = memUsedPeak();
    printf("restarts              : %"PRIu64"\n", solver.starts);
    printf("conflicts             : %-12"PRIu64"   (%.0f /sec)\n", solver.conflicts   , solver.conflicts   /cpu_time);
    printf("decisions             : %-12"PRIu64"   (%4.2f %% random) (%.0f /sec)\n", solver.decisions, (float)solver.rnd_decisions*100 / (float)solver.decisions, solver.decisions   /cpu_time);
    printf("propagations          : %-12"PRIu64"   (%.0f /sec)\n", solver.propagations, solver.propagations/cpu_time);
    printf("conflict literals     : %-12"PRIu64"   (%4.2f %% deleted)\n", solver.tot_literals, (solver.max_literals - solver.tot_literals)*100 / (double)solver.max_literals);
    if (mem_used != 0) printf("Memory used           : %.2f MB\n", mem_used);
    printf("CPU time              : %g s\n", cpu_time);
}


static Solver* solver;
// Terminate by notifying the solver and back out gracefully. This is mainly to have a test-case
// for this feature of the Solver as it may take longer than an immediate call to '_exit()'.
static void SIGINT_interrupt(int signum) { solver->interrupt(); }

// Note that '_exit()' rather than 'exit()' has to be used. The reason is that 'exit()' calls
// destructors and may cause deadlocks if a malloc/free function happens to be running (these
// functions are guarded by locks for multithreaded use).
static void SIGINT_exit(int signum) {
    printf("\n"); printf("*** INTERRUPTED ***\n");
    if (solver->verbosity > 0){
        printStats(*solver);
        printf("\n"); printf("*** INTERRUPTED ***\n"); }
    _exit(1); }

bool checkInput (int* input, int* arch_input) {

  bool input_valid = true;
  
  for (int i = 0; i < POP_INPUT*2; i++) {
    input[i] = 0;  
  }

  for (int i = 0; i < ARCH_INPUT; i++) {
    if (arch_input[i] != 0) {
      input[arch_input[i]-1] = 1;
    }
  }
  for (int i = 0; i < 4; i++) {
    if (arch_input[i] > arch_input[i+1]) {
      //arch_input[i] = arch_input[i+1];
      return false;
    }
  }
  for (int i = 7; i < 11; i++) {
    if (arch_input[i] > arch_input[i+1]) {
      //arch_input[i] = arch_input[i+1];
      return false;
    }
  }
  for (int i = 14; i < 18; i++) {
    if (arch_input[i] > arch_input[i+1]) {
      //arch_input[i] = arch_input[i+1];
      return false;
    }
  }
  for (int i = 21; i < 25; i++) {
    if (arch_input[i] > arch_input[i+1]) {
      //arch_input[i] = arch_input[i+1];
      return false;
    }
  }
  //*/
  
  int count = 0;
  for (int i = 0; i < POP_INPUT*2; i++) {
    count += input[i];    
  }
  if (count < POP_INPUT*2) input_valid = false;

  return input_valid;
}

bool setInput (int* arch_input) {

  // arch_input is a container that holds input assignments (to be turned into assumption)
  // [ 0, 0, 0,..., 0, 0] 
  // [ 1, 0, 0,..., 0, 0] 
  // [12, 0, 0,..., 0, 0] 
  // [ 0, 1, 0,..., 0, 0] 
  // [ 1, 1, 0,..., 0, 0] 
  // [12, 1, 0,..., 0, 0] 
  // [12,12, 0,..., 0, 0] 
  // [ 0, 0, 1,..., 0, 0] 
  // [ 0, 1, 1,..., 0, 0] 
  // [ 1, 1, 1,..., 0, 0] 

  
  // For each LUT, count up
  static bool flag_LUT0_finished = false;
  static bool flag_LUT1_finished = false;
  static bool flag_LUT2_finished = false;
  static bool flag_LUT3_finished = false;

  bool flag_finished = true;
  int lut_offset;

  if (flag_LUT0_finished == false) {
    lut_offset = list_of_lut_start[0];
    for (int i = 0; i < 5; i++) {
      if (arch_input[i + lut_offset] < POP_INPUT*2 - i) {
        arch_input[i + lut_offset]++;
        for (int j = i-1; j >= 0; j--) { 
          arch_input[j + lut_offset] = arch_input[i + lut_offset] + i - j;
        }
        flag_finished = false;
        return true;
      }
    } 
    if (flag_finished == true) flag_LUT0_finished = true;
  }
  
  if (flag_LUT1_finished == false) {
    lut_offset = list_of_lut_start[1];
    for (int i = 0; i < 5; i++) {
      if (arch_input[i + lut_offset] < POP_INPUT*2 - i) {
        arch_input[i + lut_offset]++;
        for (int j = i-1; j >= 0; j--) { 
          arch_input[j + lut_offset] = arch_input[i + lut_offset] + i - j;
        }
        flag_finished = false;
        lut_offset = list_of_lut_start[0];
        for (int j = 0; j < 5; j++)
          arch_input[j + lut_offset] = 5 - j;
        flag_LUT0_finished = false;
        return true;
      }
    } 
    if (flag_finished == true) flag_LUT1_finished = true;
  }

  if (flag_LUT2_finished == false) {
    lut_offset = list_of_lut_start[2];
    for (int i = 0; i < 5; i++) {
      if (arch_input[i + lut_offset] < POP_INPUT*2 - i) {
        arch_input[i + lut_offset]++;
        for (int j = i-1; j >= 0; j--) { 
          arch_input[j + lut_offset] = arch_input[i + lut_offset] + i - j;
        }
        flag_finished = false;
        flag_LUT1_finished = false;
        lut_offset = list_of_lut_start[1];
        for (int j = 0; j < 5; j++)
          arch_input[j + lut_offset] = 5 - j;
        return true;
      }
    } 
    if (flag_finished == true) flag_LUT2_finished = true;
  }
  
  if (flag_LUT3_finished == false) {
    lut_offset = list_of_lut_start[3];
    for (int i = 0; i < 5; i++) {
      if (arch_input[i + lut_offset] < POP_INPUT*2 - i) {
        arch_input[i + lut_offset]++;
        for (int j = i-1; j >= 0; j--) { 
          arch_input[j + lut_offset] = arch_input[i + lut_offset] + i - j;
        }
        flag_finished = false;
        return true;
      }
    } 
    if (flag_finished == true) flag_LUT3_finished = true;
  }
  
  
  if (flag_LUT0_finished == true &&  
      flag_LUT1_finished == true &&  
      flag_LUT2_finished == true &&  
      flag_LUT3_finished == true) return false;

  /* Simple Counting Approach (too slow)
  for (int i = 0; i < ARCH_INPUT; i++) {
    if (arch_input[i] < POP_INPUT*2) { 
      arch_input[i]++;
      for (int j = i-1; j >= 0; j--) {
        arch_input[j] = 0;
      }
      return;
    }
  }
  */
  return false;

}

void printInput (int* arch_input) {
 
  // Input sequence for the architecture
  for (int i = 0; i < ARCH_INPUT; i++) {
    printf("%2d ", arch_input[i]);
  }
  printf("\n");

}

lbool runSolve(Solver& S, vec<Lit>& lits, int* arch_input){

  long long run_count = 0;
  int print_count = 0;
  bool iter_left = true;
  double start_time = cpuTime(); 
  double end_time = cpuTime();
  
  //std::string bitmask(5,1);
  //bitmask.resize(12,0);

  std::vector<bool> t_bitmask_0;
  std::vector<bool> t_bitmask_1;
  std::vector<bool> t_bitmask_2;
  std::vector<bool> t_bitmask_3;

  for (int i = 0; i < 13; i++) {
    if (i < 5) {
      t_bitmask_0.push_back(1);
      t_bitmask_1.push_back(1);
      t_bitmask_2.push_back(1);
      t_bitmask_3.push_back(1);
    } else {
      t_bitmask_0.push_back(0);
      t_bitmask_1.push_back(0);
      t_bitmask_2.push_back(0);
      t_bitmask_3.push_back(0);
    }
  }

  //bool bitmask_0[13] = {1,1,1,1,1,0,0,0,0,0,0,0,0};
  //bool bitmask_1[13] = {1,1,1,1,1,0,0,0,0,0,0,0,0};
  //bool bitmask_2[13] = {1,1,1,1,1,0,0,0,0,0,0,0,0};
  //bool bitmask_3[13] = {1,1,1,1,1,0,0,0,0,0,0,0,0};

  do {
    do {
      do {
        do {

          run_count++; 
          //for (int i = 0; i < 12; i++) {
          //  if (t_bitmask_3[i])printf("%d ", i);
          //}
          //printf("\n");
        } while (std::prev_permutation(t_bitmask_3.begin(), t_bitmask_3.end()));
        t_bitmask_3[0] = 1;
        t_bitmask_3[1] = 1;
        t_bitmask_3[2] = 1;
        t_bitmask_3[3] = 1;
        t_bitmask_3[4] = 1;
        t_bitmask_3[5] = 0;
        t_bitmask_3[6] = 0;
        t_bitmask_3[7] = 0;
        t_bitmask_3[8] = 0;
        t_bitmask_3[9] = 0;
        t_bitmask_3[10] = 0;
        t_bitmask_3[11] = 0;
        t_bitmask_3[12] = 0;
      } while (std::prev_permutation(t_bitmask_2.begin(), t_bitmask_2.end()));
      t_bitmask_2[0] = 1;
      t_bitmask_2[1] = 1;
      t_bitmask_2[2] = 1;
      t_bitmask_2[3] = 1;
      t_bitmask_2[4] = 1;
      t_bitmask_2[5] = 0;
      t_bitmask_2[6] = 0;
      t_bitmask_2[7] = 0;
      t_bitmask_2[8] = 0;
      t_bitmask_2[9] = 0;
      t_bitmask_2[10] = 0;
      t_bitmask_2[11] = 0;
      t_bitmask_2[12] = 0;
    } while (std::prev_permutation(t_bitmask_1.begin(), t_bitmask_1.end()));
    t_bitmask_1[0] = 1;
    t_bitmask_1[1] = 1;
    t_bitmask_1[2] = 1;
    t_bitmask_1[3] = 1;
    t_bitmask_1[4] = 1;
    t_bitmask_1[5] = 0;
    t_bitmask_1[6] = 0;
    t_bitmask_1[7] = 0;
    t_bitmask_1[8] = 0;
    t_bitmask_1[9] = 0;
    t_bitmask_1[10] = 0;
    t_bitmask_1[11] = 0;
    t_bitmask_1[12] = 0;
  } while (std::prev_permutation(t_bitmask_0.begin(), t_bitmask_0.end()));

  end_time = cpuTime();
  printf("It took %fs.\n", end_time - start_time);
  printf("Run count was %ld\n", run_count);

  return l_True;
}

bool checkInput2 (int* arch_input) {
    
  int test = 0;

  for (int i = 0; i < ARCH_INPUT; i++) {
    if (arch_input[i] != -1)
      test |= 1 << arch_input[i];
  }

  return test == 0x07FE;
}

void setInputAssumptions (vec<Lit>& lits, int* arch_input) {

  int first_input_mux_lit = 57;
  int var;

  // Use assumptions to set input mux
  for (int input_mux_i = 0; input_mux_i < ARCH_INPUT; input_mux_i++) {
    for (int sel_i = 0; sel_i < ARCH_SEL_INPUT; sel_i++) {
      if (arch_input[input_mux_i] >= 0) { // 0  config, rest are inputs. -1 disconnect
        var = first_input_mux_lit + input_mux_i*5 + sel_i - 1;
        lits.push((arch_input[input_mux_i])&(1<<sel_i) ? mkLit(var) : ~mkLit(var));
      }  
    }
  }
}


void setOutputAssumptions (vec<Lit>& lits, int output_size, Solver& S) {

  int first_output_lit = 561;
  int output_lit_distance = 71;
  int var;
  bool in0[6] = {0,0,0,0,0,0};
  bool in1[6] = {0,0,0,0,0,0};
  unsigned char count = 0;

  // Input assignment to architecture
  //printf("PRINTING INPUT ARCH ASSIGNMENT\n");
  //for (int i = 0; i < POP_INPUT; i++) {
  //  printf("%d ", input[i]);
  //}
  //printf("\n");

  // Iterate through every combination of input
  // This assumes a crossbar in front of all the inputs 
  for (int input_perm = 0; input_perm < CSIZE; input_perm++) {
  
    // This assumes that the circuit is a popcount
    // Calculate the result of popcount (final count is stored in 
    //   count for this input permutation)
    count = 0;
    for (int input_i = 0; input_i < POP_INPUT; input_i++) {
      in0[input_i] = input_perm>>(input_i*2 + 0)&0x1;
      in1[input_i] = input_perm>>(input_i*2 + 1)&0x1;
      if (in0[input_i] != in1[input_i]) count += 1;
    }

    // Using the final count, set the right output value 
    for (int output_i = 0; output_i < output_size; output_i++) {
      var = first_output_lit + input_perm*output_lit_distance - 1 + output_i;
      //lits.push((count&(1<<output_i)) ? mkLit(var) : ~mkLit(var));
      S.addClause((count&(1<<output_i)) ? mkLit(var) : ~mkLit(var));

      //printf("%d 0\n", (count&(1<<output_i)) ? (var+1) : -(var+1));
    }
  }
  return;
}


//=================================================================================================
// Main:

int main(int argc, char** argv)
{
    try {
        setUsageHelp("USAGE: %s [options] <input-file> <result-output-file>\n\n  where input may be either in plain or gzipped DIMACS.\n");
        // printf("This is MiniSat 2.0 beta\n");
        
#if defined(__linux__)
        fpu_control_t oldcw, newcw;
        _FPU_GETCW(oldcw); newcw = (oldcw & ~_FPU_EXTENDED) | _FPU_DOUBLE; _FPU_SETCW(newcw);
        printf("WARNING: for repeatability, setting FPU to use double precision\n");
#endif
        // Extra options:
        //
        IntOption    verb   ("MAIN", "verb",   "Verbosity level (0=silent, 1=some, 2=more).", 1, IntRange(0, 2));
        BoolOption   pre    ("MAIN", "pre",    "Completely turn on/off any preprocessing.", true);
        StringOption dimacs ("MAIN", "dimacs", "If given, stop after preprocessing and write the result to this file.");
        IntOption    cpu_lim("MAIN", "cpu-lim","Limit on CPU time allowed in seconds.\n", INT32_MAX, IntRange(0, INT32_MAX));
        IntOption    mem_lim("MAIN", "mem-lim","Limit on memory usage in megabytes.\n", INT32_MAX, IntRange(0, INT32_MAX));

        parseOptions(argc, argv, true);
        
        SimpSolver  S;
        double      initial_time = cpuTime();

        if (!pre) S.eliminate(true);

        S.verbosity = verb;
        
        solver = &S;
        // Use signal handlers that forcibly quit until the solver will be able to respond to
        // interrupts:
        signal(SIGINT, SIGINT_exit);
        signal(SIGXCPU,SIGINT_exit);

        // Set limit on CPU-time:
        if (cpu_lim != INT32_MAX){
            rlimit rl;
            getrlimit(RLIMIT_CPU, &rl);
            if (rl.rlim_max == RLIM_INFINITY || (rlim_t)cpu_lim < rl.rlim_max){
                rl.rlim_cur = cpu_lim;
                if (setrlimit(RLIMIT_CPU, &rl) == -1)
                    printf("WARNING! Could not set resource limit: CPU-time.\n");
            } }

        // Set limit on virtual memory:
        if (mem_lim != INT32_MAX){
            rlim_t new_mem_lim = (rlim_t)mem_lim * 1024*1024;
            rlimit rl;
            getrlimit(RLIMIT_AS, &rl);
            if (rl.rlim_max == RLIM_INFINITY || new_mem_lim < rl.rlim_max){
                rl.rlim_cur = new_mem_lim;
                if (setrlimit(RLIMIT_AS, &rl) == -1)
                    printf("WARNING! Could not set resource limit: Virtual memory.\n");
            } }
        
        if (argc == 1)
            printf("Reading from standard input... Use '--help' for help.\n");

        gzFile in = (argc == 1) ? gzdopen(0, "rb") : gzopen(argv[1], "rb");
        if (in == NULL)
            printf("ERROR! Could not open file: %s\n", argc == 1 ? "<stdin>" : argv[1]), exit(1);
        
        if (S.verbosity > 0){
            printf("============================[ Problem Statistics ]=============================\n");
            printf("|                                                                             |\n"); }
        
        parse_DIMACS(in, S);
        gzclose(in);
        FILE* res = (argc >= 3) ? fopen(argv[2], "wb") : NULL;

        vec<Lit> lits;
        int first_output_lit = 561;
        int output_lit_distance = 71;
        int var;

        int arch_input[ARCH_INPUT] = {12, 11, 10, 9, 8, -1, -1, \
                      7, 6, 5, 4, 3, -1, -1, \
                      5, 4, 3, 2, 1, -1, -1, \
                      5, 4, 3, 2, 1, -1, -1};

        int output_size = ceil(log(POP_INPUT+1)/log(2));
       
        // Freeze variables that we are going to set assumptions for 
        /*for (int ioutgroup = 0; ioutgroup < CSIZE; ioutgroup++) {
          for (int iout = 0; iout < output_size; iout++) {
            var = first_output_lit + ioutgroup*output_lit_distance - 1 + iout;
            S.setFrozen(var,true);
          }
        }

        for (int iingroup = 0; iingroup < ARCH_INPUT; iingroup++) {
          for (int iin = 0; iin < 5; iin++) {
            var = 57 + iingroup * 5 - 1 + iin;
            S.setFrozen(var,true);
          }
        }*/
      
        // Preset arch_input to the lowest possible combination. 
        /*for (int i_lut = 0; i_lut < 4; i_lut++) {
          int i_arch = list_of_lut_start[i_lut];
          for (int i = 0; i < 5; i++) 
            arch_input[i_arch + i] = 5-i;
        }
        arch_input = {12, 11, 10, 9, 8, -1, -1, \
                      7, 6, 5, 4, 3, -1, -1, \
                      5, 4, 3, 2, 1, -1, -1, \
                      5, 4, 3, 2, 1, -1, -1};
       */ for (int i_6and7 = 0; i_6and7 < 8; i_6and7++) 
          arch_input[list_of_6and7_input[i_6and7]] = -1;

        if (S.verbosity > 0){
            printf("|  Number of variables:  %12d                                         |\n", S.nVars());
            printf("|  Number of clauses:    %12d                                         |\n", S.nClauses()); }
        
        double parsed_time = cpuTime();
        if (S.verbosity > 0)
            printf("|  Parse time:           %12.2f s                                       |\n", parsed_time - initial_time);

        // Change to signal-handlers that will only notify the solver and allow it to terminate
        // voluntarily:
        signal(SIGINT, SIGINT_interrupt);
        signal(SIGXCPU,SIGINT_interrupt);

        S.eliminate(true);
        double simplified_time = cpuTime();
        if (S.verbosity > 0){
            printf("|  Simplification time:  %12.2f s                                       |\n", simplified_time - parsed_time);
            printf("|                                                                             |\n"); }

        if (!S.okay()){
            if (res != NULL) fprintf(res, "UNSAT\n"), fclose(res);
            if (S.verbosity > 0){
                printf("===============================================================================\n");
                printf("Solved by simplification\n");
                printStats(S);
                printf("\n"); }
            printf("UNSATISFIABLE\n");
            exit(20);
        }

        if (dimacs){
            if (S.verbosity > 0)
                printf("==============================[ Writing DIMACS ]===============================\n");
            S.toDimacs((const char*)dimacs);
            if (S.verbosity > 0)
                printStats(S);
            exit(0);
        }
       
        lbool ret = l_Undef;
        
        /////////////////////////////////////////////////////////////////////
        // SOLVE 
        /////////////////////////////////////////////////////////////////////

        long long run_count = 0;
        int print_count = 0;
        bool iter_left = true;

        //setOutputAssumptions(lits, output_size, S);

        ret = runSolve(S, lits, arch_input);

        

        /*while (iter_left == true && (ret == l_False || ret == l_Undef)) {

          // Reset assumption list every iteration
          lits.clear();

          // Set input assumption 
          setInputAssumptions(lits, arch_input);
          if (checkInput2(arch_input)) {
            ret = S.solveLimited(lits);
          }

          //if (run_count > 10000) {
          //  end_time = cpuTime(); 
          //  printStats(S);
          //  printInput(arch_input);
          //  break;
          //}
          
          if (print_count == 0 || ret == l_True) {
            end_time = cpuTime();
            printf("still going...\n");
            printStats(S);
            printInput(arch_input);
            print_count = 100000;
          }
          run_count++;
          print_count--;

          // Increment input and check if it's the last combination
          iter_left = setInput(arch_input);
          
        }
        double total_time = end_time - start_time;
        printf("It took %f.\n", total_time);
      
        printf("\n***\t%lld\t***\n", run_count);
        */
        if (S.verbosity > 0){
            printStats(S);
            printf("\n"); }
        printf(ret == l_True ? "SATISFIABLE\n" : ret == l_False ? "UNSATISFIABLE\n" : "INDETERMINATE\n");
        if (res != NULL){
            if (ret == l_True){
                fprintf(res, "SAT\n");
                for (int i = 0; i < S.nVars(); i++)
                    if (S.model[i] != l_Undef)
                        fprintf(res, "%s%s%d", (i==0)?"":" ", (S.model[i]==l_True)?"":"-", i+1);
                fprintf(res, " 0\n");
            }else if (ret == l_False)
                fprintf(res, "UNSAT\n");
            else
                fprintf(res, "INDET\n");
            fclose(res);
        }

#ifdef NDEBUG
        exit(ret == l_True ? 10 : ret == l_False ? 20 : 0);     // (faster than "return", which will invoke the destructor for 'Solver')
#else
        return (ret == l_True ? 10 : ret == l_False ? 20 : 0);
#endif
    } catch (OutOfMemoryException&){
        printf("===============================================================================\n");
        printf("INDETERMINATE\n");
        exit(0);
    }
}
