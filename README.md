# QC_LDPC
RTL design for a "5G" multigigabit QC-LDPC pipelined encoder in System Verilog. Overall design was based on the following [research paper](#1) as well as other collected research documents 

The circuit has the ability to encode LDPC code blocks of all three of the standard lengths, _648, 1296,_ and _1944_ at a rate <ins>5/6</ins>, and uses the RU Algorithm in conjunction with extensive pipelining as well as various other discovered optimizations derived from research publications to create an high throughput QC-LDPC Encoder. 


## Included Resources
Inside ofthe source folder are included .mem files which define the base prototype matrix found in <ins>IEEE Std 802.11-2020</ins>, whose values define the shifts of the ZxZ identity matrix used to encode data found in . Each value is stored as in hexadecimal format, and the "-" values present in the prototype matrix found in the standard are replaced with the highest value of what would be the memory width required to store the matrix entires in memory as none of the Z values used for the given code block length reaches the maximum value of the data width which is used to store it inside of the defined code. _Note: These "-" values are used to define a zero matrix instead of a shift of the ZxZ identity matrix_  


<style>
table th:first-of-type {
    width: 10%;
}
table th:nth-of-type(2) {
    width: 20%;
}
table th:nth-of-type(3) {
    width: 20%;
}

</style>

## QC LDPC Parameters defined by the standard
| Coding Rate  | Information Block Bits | Total Codeword Bits
| :-----: | :-----: | :-----: |
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



## References
<a id="1">[1]</a> 
Y. Jung, C. Chung, J. Kim, and Y. Jung, “7.7Gbps encoder design for IEEE 802.11n/ac Qc-LDPC codes,” 2012 International SoC Design Conference (ISOCC), pp. 215–218, Nov. 2012. doi:10.1109/isocc.2012.6407078 
