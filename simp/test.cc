#include "stdio.h"

#define CSIZE 4096 
#define POP_INPUT 6
#define ARCH_INPUT 28 
#define ARCH_SEL_INPUT 5 

const int list_of_6and7_input[8] = {5, 6, 12, 13, 19, 20, 26, 27};
const int list_of_lut_start[4] = {0, 7, 14, 21};
bool setInputNoWaste (int* arch_input) {

  // Count without combinations that don't work
  // 8 7 6 5 4 -1 -1 3 2 1 0 0 -1 -1
  // 8 7 6 5 3 -1 -1 4 2 1 0 0 -1 -1
  // 8 7 6 5 4 -1 -1 4 3 2 1 0 -1 -1
  // 8 7 6 5 4 -1 -1 5 3 2 1 0 -1 -1
  
  static int curr_i = POP_INPUT*2;
  //static int curr_i = POP_INPUT*2%5;
  static int curr_array_i = POP_INPUT*2/5;

  static int curr_array[4][POP_INPUT*2] = {
      {8,9,10,11,12,-1,-1,-1,-1,-1,-1},
      {3,4,5,6,7,8,9,10,11,12,-1,-1},
      {1,2,3,4,5,6,7,8,9,10,11,12},
      {1,2,3,4,5,6,7,8,9,10,11,12}};
  static int max_val_i[4] = {4,9,11,0};
  int temp_arch_input[ARCH_INPUT] =
      {4, 3, 2, 1, 0, -1, -1, \
       4, 3, 2, 1, 0, -1, -1, \
       1, 0, -1, -1, -1, -1, -1, \
       4, 3, 2, 1, 0, -1, -1};
  
  // Iterate through each LUT starting from
  //  the current LUT.
  for (int lut_i = curr_array_i; lut_i >=0; lut_i++) {

    // Iterate through each inputs of the LUT
    //  and increment if it's below max input #
    //  else continue till you find one
    int lut_offset = list_of_lut_start[lut_i];
    for (int i = 0; i < 5; i++) {
      int check_idx = temp_arch_input[lut_offset + i];
      int max_val = curr_array[lut_i][max_val_i[lut_i]];
      if (arch_input[lut_offset + i] < max_val) {
        
        // Increment array_item index to get the next high value
        // Set the next input to the new high value
        int next_idx = temp_arch_input[lut_offset + i]++;
        arch_input[lut_offset + i] = curr_array[lut_i][next_idx];

        // A number of incremented, fix all the other
        //  numbers according to this
        for (int j = i-1; j >= 0; j--) {
          arch_input[lut_offset + j] = arch_input[lut_offset + i] + i - j;
        }

        for (int k = lut_i-1; k >= 0; k--) {
          for (int j = 0; j < 12; j++) {
            curr_array[k][j] = 1; 
          }
        }
        for (int j = 0; j < 28; j++)
          printf("%d ", arch_input[j]);
        for (int j = 0; j < 4; j++) {
          for (int k = 0; k < 12; k++) {
            printf("%d ", curr_array[j][k]);
          }
          printf("\n");
        }
        return true;
      }
    } 
  }

  // If you didn't increment anything,
  //  move to the next iteration set
  curr_i++;
 
  if (curr_i < 28 ) return true;
  else return false; 

} 



int test() {

  int arch_input[ARCH_INPUT] = {12, 11, 10, 9, 8, -1, -1, \
                7, 6, 5, 4, 3, -1, -1, \
                5, 4, 3, 2, 1, -1, -1, \
                5, 4, 3, 2, 1, -1, -1};

  bool cont = true;
  int count = 0;

  while (count < 100 && cont) {
    cont = setInputNoWaste(arch_input);
    count++;
  }

  return 0 ;
}
