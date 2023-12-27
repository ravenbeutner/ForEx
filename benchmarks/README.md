# Benchmarks

This file contains instructions on how to reproduce the experimental results in [1]. 
To execute the scripts in this folder, your current directory _must_ be `benchmarks/`. 


## Comparing with HyPA

The verification instances from [2, Table 2] (translated into the syntax supported by ForEx) are located in the `hypa/` folder. 
To run all instances automatically, run `python run_hypa.py`.


## Comparing with PCSAT 

The GNI verification instances from [3] are located in the `pcsat/` folder.
To run all instances automatically, run `python run_pcsat.py`.

## Comparing with HyPro 

The verification instances from [4] are located in the `hypro/` folder.
To run all instances automatically, run `python run_hypro.py`.


## Comparing with HyPA on k-Safety Instances

The supported verification instances from [2, Table 1] are located in the `k_safety/` folder. 
To run all instances automatically, run `python run_k_safety.py`.


## References  

[1] Automated Software Verification of Hyperliveness. Raven Beutner. TACAS 2024

[2] Software Verification of Hyperproperties Beyond k-Safety. Raven Beutner, Bernd Finkbeiner. CAV 2023

[3] Constraint-Based Relational Verification. Hiroshi Unno, Tachio Terauchi, Eric Koskinen. CAV 2021

[4] Prophecy Variables for Hyperproperty Verification. Raven Beutner, Bernd Finkbeiner. CSF 2023
