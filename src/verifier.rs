mod fields;
mod merkle;
use crate::merkle::merkle::{compute_hash_one,verify_opening};
use ark_poly::Polynomial;
use ark_poly::{univariate::DensePolynomial}; 
use ark_ff::{PrimeField};
use spongefish::codecs::arkworks_algebra::*;  
use std::env;

use mini_stark::{
    FpGoldilocks,
    parse_proof,
    generate_evaluation_domain,
    get_bounded_index,
    multiply_by_coset,
    fold_domain,
    lagrange_interpolation,
    add_sample_index_challenge,
    initialize_domain_separator
};

//Convert FpGoldilocks to usize
fn unsafe_goldilocks_to_usize(x: FpGoldilocks) -> usize {
    x.into_bigint().0[0] as usize
}

fn verify_commitment(commit_index:usize, commit_val_hash:FpGoldilocks, authentication_paths:Vec<FpGoldilocks>,merkle_root:FpGoldilocks){

    // //Verifier opens proof at the value
    let is_valid_opening:bool = verify_opening(commit_index,commit_val_hash,&authentication_paths,&merkle_root);
    assert_eq!(is_valid_opening,true);
}

//Check if proof string is empty or not
fn check_proof_string(proof:&str)->&str{
    if proof.is_empty(){
        panic!("No proof string found!!!");
    }
    proof
}

// Collinearity test
fn collinearity_test(w_i:FpGoldilocks,minus_w_i:FpGoldilocks,unfolded_commit_value_one:FpGoldilocks,unfolded_commit_value_two:FpGoldilocks,folded_commit_value:FpGoldilocks,r_challenge:FpGoldilocks){

    //Collinearity test
    // A = (w^i,f(w^i)), B = (-w^i,f(w^N/2+i)), C = (r, folded_f((w^i))^2)
    let x_list = vec![
        w_i,
        minus_w_i,
    ];
    let y_list = vec![
        unfolded_commit_value_one,
        unfolded_commit_value_two,
    ];

    let a_b_poly:DensePolynomial<FpGoldilocks> = lagrange_interpolation(&x_list,y_list); //Intepolate A,B 
    let a_b_poly_eval = a_b_poly.evaluate(&r_challenge); //Colinearity test
    assert_eq!(a_b_poly_eval,folded_commit_value); // eval ===? f(w^i)^2
}

//Parse proof round by round
fn parse_proof_round_by_round(proof_elements_vr:Vec<FpGoldilocks>)->Vec<Vec<Vec<FpGoldilocks>>>{
    let mut temp_proof_list:Vec<FpGoldilocks> = Vec::new();
    let mut proof_list_vr:Vec<Vec<FpGoldilocks>> = Vec::new();
    let mut proof_list_round_vr:Vec<Vec<Vec<FpGoldilocks>>> = Vec::new(); // Roundwise proof elements
    let mut auth_path_len_index:usize = 2; //[Root(0),commitval(1),authpathlen(2)] (Initialize)
    let mut split_index:usize = 999;

    for index in 0..proof_elements_vr.len(){
        //Constant value in last 
        if index+1 == proof_elements_vr.len(){
            proof_list_round_vr.push(vec![vec![proof_elements_vr[index]]]);
            break;
        }

        //First proof format : [Root,index,authpathlen,authpaths]
        if index == auth_path_len_index {
            let auth_path_len = proof_elements_vr[index];

            split_index = auth_path_len_index + unsafe_goldilocks_to_usize(auth_path_len);
            
            //Update authpathlen index
            if proof_list_vr.len() % 2 == 0{ //List is even then folded round left

                auth_path_len_index = split_index+2; 
            }else{//Odd
                auth_path_len_index = split_index+3;
            }
        }
        temp_proof_list.push(proof_elements_vr[index]);

        //List split per part of a round
        if index == split_index{
            proof_list_vr.push(temp_proof_list);
            temp_proof_list = vec![]; //Empty list

            //If round completed
            if proof_list_vr.len() == 3{
                //Push to final 
                proof_list_round_vr.push(proof_list_vr);
                //Empty the list
                proof_list_vr = vec![];
            }

        }        
    }
    proof_list_round_vr
}

// Fiat shamir challenges
fn fiat_shamir_challenges(transcript:Vec<FpGoldilocks>,N:usize,composition_merkle_root:FpGoldilocks)->(ProverState,[FpGoldilocks;3]){
    let mut prover_state = initialize_domain_separator(transcript.len(), N);

    // Add transcript
    prover_state.add_scalars(&transcript).expect("Fiat shamir error!! Scalar addition failed");  
    let [coset_fp]: [FpGoldilocks; 1] = prover_state.challenge_scalars().expect("Fiat shamir error!! Challenge genration failed");    
  
    // Generate challenge for composition
    prover_state.add_scalars(&[coset_fp]).expect("Fiat shamir error!! Scalar addition failed"); 
    let [_,_,_,_,_]: [FpGoldilocks; 5] = prover_state.challenge_scalars().expect("Fiat shamir error!! Challenge genration failed");  

    //Sample for linear combination in folded polynomial
    prover_state.add_scalars(&[composition_merkle_root]).expect("Fiat shamir error!! Scalar addition failed"); 
    let [r_challenge]: [FpGoldilocks; 1] = prover_state.challenge_scalars().expect("Fiat shamir error!! Challenge genration failed");  
    
    //Sample random index 'i' for query
    prover_state.add_scalars(&[r_challenge]).expect("Fiat shamir error!! Scalar addition failed");  
    let [index_challenge]: [FpGoldilocks; 1] = prover_state.challenge_scalars().expect("Fiat shamir error!! Challenge genration failed");  

    (prover_state,[coset_fp,r_challenge,index_challenge])
}
fn main(){
	//Read proof 
    let args: Vec<String> = env::args().collect();
    let proof_string = check_proof_string(&args[1]);
    let parsed_proof = parse_proof(proof_string);
    let proof_elements_vr = parsed_proof[1..].to_vec();
    let composition_merkle_root = parsed_proof[0];    

    // Fibbonaci execution trace (Size: 2^k)
    let execution_trace:Vec<FpGoldilocks> = vec![
        FpGoldilocks::from(0),
        FpGoldilocks::from(1),
        FpGoldilocks::from(1),
        FpGoldilocks::from(2),
        FpGoldilocks::from(3),
        FpGoldilocks::from(5),
        FpGoldilocks::from(8),
        FpGoldilocks::from(13),
    ];

    let blowupfactor:usize = 4; // Larger the blowupfactor better the soundness
    let T = execution_trace.len(); //Trace length (dimension k in RS code)
    let N = blowupfactor * T; //Size for extension domain

    //Evaluation domain (Roots of unity) of size
    let roots_unity_T:Vec<FpGoldilocks> = generate_evaluation_domain(T);

    //Low degree extension
    let roots_unity_N:Vec<FpGoldilocks> = generate_evaluation_domain(N);

    //Transcript (Public)
    let mut t_0:Vec<FpGoldilocks> = roots_unity_T;
    let mut t1:Vec<FpGoldilocks> = roots_unity_N.clone();
    t_0.append(&mut t1);
    let transcript:Vec<FpGoldilocks> = t_0;

    let (mut prover_state,[coset_fp,r_challenge,index_challenge]) = fiat_shamir_challenges(transcript, N, composition_merkle_root);
    
    let mut unfolded_evaluation_domain:Vec<FpGoldilocks> = multiply_by_coset(&roots_unity_N,coset_fp); //Low degree extension of roots of unity domain
    let proof_list_round_vr = parse_proof_round_by_round(proof_elements_vr);    
    let mut unfolded_domain_size = N;
    let mut prev_round_root:FpGoldilocks = FpGoldilocks::from(0);
    let mut sample_query_index = index_challenge;

    //Round by round FRI verification
    for (round,round_list) in proof_list_round_vr.iter().enumerate(){

        //Last round
        if round+1 == proof_list_round_vr.len(){//Last round
            continue;
        }  
        
        if round == 0{ // First round
            let unfolded_root_vr = round_list[0][0];
            let unfolded_commit_value_one = round_list[0][1];
            let unfolded_authentication_path_one = &round_list[0][3..];
            
            let unfolded_commit_value_two = round_list[1][0];
            let unfolded_authentication_path_two = &round_list[1][2..];
            
            let folded_root_vr = round_list[2][0];
            let folded_commit_value = round_list[2][1];
            let folded_authentication_path = &round_list[2][3..];
            
            let folded_query_index = get_bounded_index(sample_query_index,(unfolded_domain_size/2)-1);

            verify_commitment(folded_query_index, compute_hash_one(unfolded_commit_value_one), unfolded_authentication_path_one.to_vec(), unfolded_root_vr);
            verify_commitment((N/2)+folded_query_index, compute_hash_one(unfolded_commit_value_two), unfolded_authentication_path_two.to_vec(), unfolded_root_vr);
            verify_commitment(folded_query_index, compute_hash_one(folded_commit_value), folded_authentication_path.to_vec(), folded_root_vr);

            //Collinearity test
            collinearity_test(
                unfolded_evaluation_domain[folded_query_index],
                unfolded_evaluation_domain[(unfolded_domain_size/2) + folded_query_index],
                unfolded_commit_value_one,
                unfolded_commit_value_two, 
                folded_commit_value, 
                r_challenge
            );

            //Add scalar for new challenge
            sample_query_index = add_sample_index_challenge(&mut prover_state,folded_root_vr);

            //Update previous root
            prev_round_root = folded_root_vr;
        }else{

            //Other rounds
            let unfolded_root_vr = prev_round_root;
            // let unfolded_query_index_one = round_list[0][0];
            let unfolded_commit_value_one = round_list[0][0];
            let unfolded_authentication_path_one = &round_list[0][2..];
            
            // let unfolded_query_index_two = round_list[1][0];
            let unfolded_commit_value_two = round_list[1][0];
            let unfolded_authentication_path_two = &round_list[1][2..];
            
            let folded_root_vr = round_list[2][0];
            // let folded_query_index = round_list[2][1];
            let folded_commit_value = round_list[2][1];
            let folded_authentication_path = &round_list[2][3..];

            let folded_query_index = get_bounded_index(sample_query_index,(unfolded_domain_size/2)-1);

            verify_commitment(folded_query_index, compute_hash_one(unfolded_commit_value_one), unfolded_authentication_path_one.to_vec(), unfolded_root_vr);
            verify_commitment((unfolded_domain_size/2) + folded_query_index,compute_hash_one(unfolded_commit_value_two), unfolded_authentication_path_two.to_vec(), unfolded_root_vr);
            verify_commitment(folded_query_index, compute_hash_one(folded_commit_value), folded_authentication_path.to_vec(), folded_root_vr);

            //Collinearity test
            collinearity_test(
                unfolded_evaluation_domain[folded_query_index],
                unfolded_evaluation_domain[(unfolded_domain_size/2) + folded_query_index],
                unfolded_commit_value_one,
                unfolded_commit_value_two, 
                folded_commit_value, 
                r_challenge
            );

            if unfolded_domain_size > 2{
                //Next round will have a constant so no sampling is required
                sample_query_index = add_sample_index_challenge(&mut prover_state,folded_root_vr);
            }

            //Update prev root
            prev_round_root = folded_root_vr;
        }
        unfolded_domain_size = unfolded_domain_size/2;
        unfolded_evaluation_domain = fold_domain(&unfolded_evaluation_domain);

    }

}