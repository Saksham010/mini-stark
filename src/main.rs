use std::{hash::{DefaultHasher, Hash, Hasher}, vec};

//Computes hash(a,b)
fn compute_hash(t:u64,t2:u64)->u64{
    let mut s = DefaultHasher::new();
    t.hash(&mut s);
    t2.hash(&mut s);
    s.finish()
}

//Compute hash(a)
fn compute_hash_one(t:u64)->u64{
    let mut s = DefaultHasher::new();
    t.hash(&mut s);
    s.finish()
}

//Return hashed leaf values
fn compute_has_list(leaf_arr:&Vec<u64>)->Vec<u64>{
    let mut hashed_leaf_arr:Vec<u64> = Vec::new();
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
fn commit(mut leaf_arr_h:Vec<u64>)->u64 {
    let mut N = leaf_arr_h.len();
    while N > 1{
        for i in (0..N).step_by(2){
            let parent_hash: u64 = compute_hash(leaf_arr_h[i],leaf_arr_h[get_min(i+1,N-1)]);
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
fn compute_sibling_values(mut val_idx:usize,mut leaf_arr_h:Vec<u64>)->Vec<u64>{

    let mut N = leaf_arr_h.len();
    let mut k:usize = 0;
    let mut authentication_paths:Vec<u64> = Vec::new();

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
            let parent_hash: u64 = compute_hash(leaf_arr_h[i],leaf_arr_h[get_min(i+1,N-1)]);
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
fn verify_opening(mut opening_idx:usize,opening_value:u64,authentication_paths:&Vec<u64>,merkle_root:&u64)->bool{
    let mut hash_val:u64 = compute_hash_one(opening_value);

    for sibling in authentication_paths{
        if opening_idx %2 == 0 {
            //Even -> sibling is right
            let left:u64 = hash_val;
            let right:u64 = *sibling;
            let parent_hash = compute_hash(left, right);
            hash_val = parent_hash;

        }else{
            //Odd -> Sibling on left
            let left:u64 = *sibling;
            let right:u64 = hash_val;
            let parent_hash = compute_hash(left, right);
            hash_val = parent_hash;
        }
        
        if opening_idx %2 ==0 {opening_idx /= 2} else{opening_idx = (opening_idx-1)/2}
    }
    if *merkle_root == hash_val {
        true
    }else{false}
}

fn main() {

    //Prover computes merkle root
    let leaf_arr:Vec<u64> = vec![10,20,30,40,50,60,70];
    let leaf_arr_hash:Vec<u64> = compute_has_list(&leaf_arr);
    let merkle_root = commit(leaf_arr_hash.clone());
    println!("Merkle root of commitment: {:?}",merkle_root);

    // Compute sibling values
    let val_proof_idx:usize = 3; //30
    let val_proof:u64 = leaf_arr[val_proof_idx]; // Value to send to prover to prove commitment of the root
    let authentication_paths:Vec<u64> = compute_sibling_values(val_proof_idx, leaf_arr_hash.clone());
    println!("Authentication paths: {:?}",authentication_paths);

    //Verifier opens proof at the value
    let is_valid_opening:bool = verify_opening(val_proof_idx,val_proof,&authentication_paths,&merkle_root);
    println!("Merkle root validation: {:?}",is_valid_opening);
}
