# QC_LDPC
RTL design for a "5G" multigigabit QC-LDPC pipelined encoder in System Verilog. 

Implements code length of 1296, at a rate of 5/6, and uses the RU Algorithm in conjunction with various other optimizations derived from research publications to create an high throughput QC-LDPC Encoder. 

#QC LDPC Parameters defined by the standard
| Coding rate (R) | ,LDPC information block length (bits) | LDPC codeword block length(bits)
| ------------- | ------------- |
| 1/2  | 972  | 1944  |
| 1/2  | 648  | 1296  |
| 1/2  | 324  | 648  |
| 2/3  | 129  | 1944 |
| 2/3  | 864  | 1296  |
| 2/3  | 432  | 648  |
| 3/4  | 145  | 1944  |
| 3/4  | 972  | 1296  |
| 3/4  | 486  | 648  |
| 5/6  | 162  | 1944  |
| 5/6  | 108  | 1296  |
| 5/6  | 540  | 648  |

This Project includes .mem files which define the base parity matrix whose values define the shifts of the ZxZ identity matrix used to encode data. Each value is stored as a hex, and the - values present in the defined matrix found in the standard are replaced with the highest value of what would be the memory width required to store the matrix entires in memory. 