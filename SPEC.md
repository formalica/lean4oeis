# PARSER
write lean pure code or macro based code which parses raw math formulas(now only is but later we will parse latex and wolfram) and return lean code which than can be used to generate lean files. excet semiformal formulas text of formulas can also contain human words, different unrealated symbols. code should be extendable code so that it will later be used to add new built-in functions, parser should pick simplest interpritation of sqrt(first will try Nat.sqrt then Int.sqrt then Real.sqrt) so it should provide iterator over interpretations and we can check them against computed sequence data values . write tests for generate_lseq function which will test it against few oeis sequences and return content of Defs, Equiv_hash, Data, Basic_hash files and test should run write it in file system and run from lean and check wheather it compiles. you can create Defs file first by defining main defintions by sorry and then parse each main definition and edit that files to fill main definition and then able to typecheck even if this definition depends from definition of other sequence which definition is still filled by sorry.

there should be intermeddiate ast representation of formulas and then we can generate lean code from that ast. note that later we will convert full ast of wolfram to this intermediate ast and also parse latex to this ast, so you architecture should be extendable. write some typeinference logic for that ast to infer types of each part of expression and quickly choose right interpretation from possible interpritations of given function. note that oeis main function can have 3 interpretations, main function with Nat,Int or subtype, fn which argument is always Nat and fz which argument is always Int, and main function is always preferable if it is possible to use, if it is not possible then we can use others. somehow we need to understant wheather given formula is fully defining given sequence or it is just property of sequence. depending on it we need to generate def or theorem. we can use existing data to check which interpretation of given formula is correct and also whether given formula is fully defining sequence or just property of sequence.


- sometimes expression can contain intermediate real number, rational and integer numbers but final result will always be Nat. for example this one (n-2)*2^(n-1). so we can not interpret n-1 as Nat. so we should also give data and he can decide which interpretation holds

- A084847: a(n) = 2*3^n+2^(2n-1)*(n-2). is hard if we want to have Nat->Nat, because of the negative intermediate values for n=0 and n=1 because we expect 1 and 4 results for them. even for Nat->Int, we have rational intermediate values for n=0 and n=1.



- A027599: a(n) = 3*n^2 - 7*n + 6. should be converted to fun n => 3 * (n ^ 2) + 6 - 7 * n because 3 * (n ^ 2) - 7 * n can be 0 if 3 * (n ^ 2) s small than 7*n
 TODO we have big problem here, because  fun n => 3 * n ^ 2 - 7 * n + 6 formalization works for n>=2 and llm may decide to to add special if conditions for for n=0,1 and leave base case 3 * n ^ 2 - 7 * n + 6, which will work but it is not simplest formula. so we just need to write all additions and then substructions  






# OVERALL ARCHITECTURE


for each oeis sequence(like A1234560 we should create following files in A123/A123456 directory)
 
Defs.lean file should contain most simple preferably computable defintions from header, if there is no computable definition then we should define it via proposition. if defintion contain Real then it is still computable, by saying non computable I mean it is defined as proposition and it takes argument and result. 

Equiv_hash.lean should contain alternative defintion of sequence and also theorem that given defintion are equivalent to main deintion from Defs.lean file. header also can contain few defintions, so except main defintion we should create Equiv_hash.lean files for each other defintion. we should create separate files for each forumal from formulas section too. if one statement is from header or formulas section is chain of equalities between definitions of same sequence then we need to create definition from each of them. 
 
Basic_hash.lean should contain theorem which does not definitely define sequence and prove some of its properties or relations to other sequences, in other words formulas from formula section which is not definition of sequence
 
if theorem is not proved then it should contain wrapper over interval cases tactic which proves that it satisfies to the known values of sequences, otherwise this tactics should fail if at least one of them does not satisfied 
 
Data.lean contain data




write generate_lseq function in lean4 which takes human written header/title of OEIS sequence and also list of human written formulas, array of computaed values of that sequence and offset of index from which sequence starts
for each oeis sequence(like A1234560 we should create following files in A123/A123456 directory) 
 
 
if main definition of sequence is defined by sorry, then prove data_eq theorem by sorry too,  
in case equivalence and basic theorems will need to have tactic which will interval check theorem against available data values and fails if at least one of them does not satisfies. if it satidies to all data points then it should not fail and then just finish proof by sorry(later it will be proved and interval cheks will be deleted because they no longer needed). 
 


add new fields to following tables if you think it is necessary. not that we will run your scripts reguraly and we need to store information which is necessary and should persist between runs

keep some metadata table where you will store information about each sequence, like its name, offset, data, formalized_formula_hashes, unformalized_formula_hashes, main_definition_hash, all_unformalized_formulas_text(at first this should be list of lines of all formulas. in next stage we should parse all non prop definitions and after it cut that forumals(or replace with ..... 5 dots) from this text and after that we will only have the remaining unformalized formulas. we doing this because some formulas canbe property based multiline defintions, but if we will interpret each line as separate formula then we will misinterpret each line of that formulas as property of sequence and we will misleadingly include them in Basic_hash.lean files, while all this lines are connected and they are part of same alternative full defintion. in second stage we will give llm reminaing text and say to find full defintions and create defintions from them and then we will remove them from this text too. after all of this, remaing text will only contain formulas which is just properties sequences and not full definitions)

separate formula table where you will store information about each formula, like its hash, oeis_name, human_written_formula, formalized_formula, type(it can be computable_defintion, prop_definition, basic_theorem(theorem about sequence property whihch  no sufficient to define sequence)), status(STATUS_PROVED for defintions we need to prove equicvalence to main definition, for basic theorem we need to prove its statement, STATUS_VEFIFIED if it is not proved and only verified for given values, STATUS_SORRY if it is not proved and only verified for given values),  verification_values(list of values for which it is verified), disproved_values(list of values for which it is disproved), additional_conditions(if defintion or theorem is not general and it is only valid for some values of n, then we need to store this information and inject it into generated code as assumption of theorem or via special cases of match expression)