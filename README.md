# YoctoDao
This is what we consider to be the most basic building block in creating organizations on-chain.

The contract is parameterized by the AssetClass required for voting. In our case this is https://cardanoscan.io/token/5b01968867e13432afaa2f814e1d15e332d6cd0aa77e350972b0967d476f76546f6b656e

Additionally a hard-coded value is used to determine the number of tokens from the AssetClass above that are required in order to spent UTxOs from the script address. An NFT denoting the identity of a DAO can be stored at this script and Governance Tokens can be distributed to members who can then vote upon future updates to the system.

We are currently in the process of conducting our first vote to raise the minimum required Governance Tokens to spend the UTxOs at the script.

Future improvements include the ability to vote using separate transactions for each individual that is a part of the voting process.

# Deploying
First off, I would recommend going through this repository and doing at least some of the exercises to familiarize yourself with getting plutus code running on-chain.
https://github.com/input-output-hk/Alonzo-testnet/tree/main

Inside of the Fracada repository from DcSpark there is a file that they use for compiling the plutus script, this was very helpful for us to get our code on-chain.
https://github.com/dcSpark/fracada/blob/main/exe/script-dump.hs

Once you have the validator.plutus file 
