# QC_LDPC
RTL design for a "5G" multigigabit QC-LDPC pipelined encoder in System Verilog. 

Implements code length of 1296, at a rate of 5/6, and uses the RU Algorithm in conjunction with various other optimizations derived from research publications to create an high throughput QC-LDPC Encoder. 

The goal of this project was to put one together as quickly (yet still accurate) as possible. 



This Project includes .mem files which define the base parity matrix whose values define the shifts of the ZxZ identity matrix used to encode data. Each value is stored as a hex, and the - values present in the defined matrix found in the standard are replaced with the highest value of what would be the memory width required to store the matrix entires in memory. 