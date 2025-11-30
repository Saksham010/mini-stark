use crate::FpGoldilocks;
use spongefish::{DomainSeparator, DefaultHash};  
use spongefish::codecs::arkworks_algebra::*;  

pub fn compute_hash_one(t: FpGoldilocks) -> FpGoldilocks {  
    let mut domsep = <DomainSeparator<DefaultHash> as FieldDomainSeparator<FpGoldilocks>>::add_scalars(
        DomainSeparator::<DefaultHash>::new("hash-one"),
        1,
        "hash_input",
    );

    domsep = <DomainSeparator<DefaultHash> as FieldDomainSeparator<FpGoldilocks>>::challenge_scalars(
        domsep,
        1,               // number of scalars for the challenge
        "hashed_val",         // label for the challenge
    );

    let mut prover_state = domsep.to_prover_state();

    prover_state.add_scalars(&[t]).expect("Hashing error!! Scalar addition failed");  

    let [result]:[FpGoldilocks;1] = prover_state.challenge_scalars().unwrap();  
    result  
}

//Computes hash(a,b)
fn compute_hash(a: FpGoldilocks, b: FpGoldilocks) -> FpGoldilocks {
    let mut domsep = <DomainSeparator<DefaultHash> as FieldDomainSeparator<FpGoldilocks>>::add_scalars(
        DomainSeparator::<DefaultHash>::new("hash-two"),
        2,
        "hash_input",
    );

    domsep = <DomainSeparator<DefaultHash> as FieldDomainSeparator<FpGoldilocks>>::challenge_scalars(
        domsep,
        1,               // number of scalars for the challenge
        "hashed_val",         // label for the challenge
    );

    let mut prover_state = domsep.to_prover_state();

    prover_state.add_scalars(&[a,b]).expect("Hashing error!! Scalar addition failed");  

    let [result]:[FpGoldilocks;1] = prover_state.challenge_scalars().unwrap();  
    result  
}

//Return hashed leaf values
pub fn compute_hash_list(leaf_arr:&Vec<FpGoldilocks>)->Vec<FpGoldilocks>{
    let mut hashed_leaf_arr:Vec<FpGoldilocks> = Vec::new();
    for leaf in leaf_arr{
        hashed_leaf_arr.push(compute_hash_one(*leaf));
    }
    hashed_leaf_arr
}

// Return min(a,b)
fn get_min(a:usize,b:usize)->usize{
    if a < b {return a}
    return b
}

//Returns merkle roots of commitment
pub fn commit(mut leaf_arr_h:Vec<FpGoldilocks>)->FpGoldilocks {
    let mut N = leaf_arr_h.len();
    while N > 1{
        for i in (0..N).step_by(2){
            let min:usize = get_min(i+1,N-1);
            let parent_hash: FpGoldilocks = compute_hash(leaf_arr_h[i],leaf_arr_h[min]);
            leaf_arr_h[i/2] = parent_hash;
        }

        //If even number of leaves
        if N%2 == 0{
            N = N/2
        }else{
            N = (N+1)/2
        }
    }

    leaf_arr_h[0]
}

//Returns authentication paths for commited value
pub fn compute_sibling_values(mut val_idx:usize,mut leaf_arr_h:Vec<FpGoldilocks>)->Vec<FpGoldilocks>{

    let mut N = leaf_arr_h.len();
    let mut k:usize = 0;
    let mut authentication_paths:Vec<FpGoldilocks> = Vec::new();

    while N > 1{
        
        if val_idx %2 ==0 {
            //Even -> Then sibling is on the right
            k = get_min(val_idx+1, N-1);
        }else{
            //Odd -> Sibling is on the left
            k = val_idx-1;
        }

        //Save the sibling value
        authentication_paths.push(leaf_arr_h[k]);

        if val_idx%2 ==0 {val_idx = val_idx/2} else{val_idx = (val_idx-1)/2}

        //Reconstruct parent hash
        for i in (0..N).step_by(2){
            let parent_hash: FpGoldilocks = compute_hash(leaf_arr_h[i],leaf_arr_h[get_min(i+1,N-1)]);
            leaf_arr_h[i/2] = parent_hash;
        }

        //If even number of leaves
        if N%2 == 0{
            N = N/2
        }else{
            N = (N+1)/2
        }
    }

    authentication_paths

}

// Verify merkle root at opening value
pub fn verify_opening(mut opening_idx:usize,opening_value_hash:FpGoldilocks,authentication_paths:&Vec<FpGoldilocks>,merkle_root:&FpGoldilocks)->bool{
    // let mut hash_val:FpGoldilocks = compute_hash_one(opening_value);
    let mut hash_val:FpGoldilocks = opening_value_hash;

    for sibling in authentication_paths{
        if opening_idx %2 == 0 {
            //Even -> sibling is right
            let left:FpGoldilocks = hash_val;
            let right:FpGoldilocks = *sibling;
            let parent_hash = compute_hash(left, right);
            hash_val = parent_hash;

        }else{
            //Odd -> Sibling on left
            let left:FpGoldilocks = *sibling;
            let right:FpGoldilocks = hash_val;
            let parent_hash = compute_hash(left, right);
            hash_val = parent_hash;
        }
        
        if opening_idx %2 ==0 {opening_idx /= 2} else{opening_idx = (opening_idx-1)/2}
    }
    if *merkle_root == hash_val {
        true
    }else{false}
}