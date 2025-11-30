mod fields;
mod merkle;
use ark_poly::{univariate::DensePolynomial,DenseUVPolynomial}; 
use spongefish::codecs::arkworks_algebra::*;  
use std::ops::{Mul};

use crate::merkle::merkle::{
    commit,
    compute_hash_list,
    compute_hash_one,
    compute_sibling_values
};

use mini_stark::{
    FpGoldilocks,
    generate_evaluation_domain,
    lagrange_interpolation,
    multiply_by_coset,
    get_fp_in_poly,
    get_shifted_poly,
    get_x_n_poly,
    evaluate_poly_from_domain,
    fold_domain,
    get_bounded_index,
    verify_commitment,
    merge_list,
    concatenate_proof_string,
    initialize_domain_separator,
    add_sample_index_challenge
};


//Convert list in fp_list
fn get_fp_from_list(u64_list:&Vec<u64>)->Vec<FpGoldilocks>{
    let mut fp_list:Vec<FpGoldilocks> = Vec::new();
    for val in u64_list{
        fp_list.push(FpGoldilocks::from(*val));
    }
    fp_list
}


// Fiat shamir challenges
fn fiat_shamir_challenges_one(transcript:Vec<FpGoldilocks>,N:usize)->(ProverState,[FpGoldilocks;6]){

    let mut prover_state = initialize_domain_separator(transcript.len(), N);

    // Add transcript
    prover_state.add_scalars(&transcript).expect("Fiat shamir error!! Scalar addition failed");  
    let [coset_fp]: [FpGoldilocks; 1] = prover_state.challenge_scalars().expect("Fiat shamir error!! Challenge genration failed");    
  
    // Generate challenge for composition
    prover_state.add_scalars(&[coset_fp]).expect("Fiat shamir error!! Scalar addition failed"); 
    let [alpha0,alpha1,alpha2,alpha3,alpha4]: [FpGoldilocks; 5] = prover_state.challenge_scalars().expect("Fiat shamir error!! Challenge genration failed");  

    (prover_state,[coset_fp,alpha0,alpha1,alpha2,alpha3,alpha4])
}

// Get even and odd coeff
fn get_even_odd_coeff(coeff_list:&Vec<FpGoldilocks>)->(Vec<FpGoldilocks>,Vec<FpGoldilocks>){
    let mut even_coeffs:Vec<FpGoldilocks> = Vec::new();
    let mut odd_coeffs:Vec<FpGoldilocks> = Vec::new();
    let mut index:usize = 0;
    for c in coeff_list{
        //Even coeffcients
        if index%2 == 0{
            even_coeffs.push(*c);
        }else{
            odd_coeffs.push(*c);
        }
        index = index+1;
    }
    (even_coeffs,odd_coeffs)
}
fn main() {

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

    // Interpolation
    let x:Vec<FpGoldilocks> = roots_unity_T.clone();
    let y:Vec<FpGoldilocks> = execution_trace.iter().map(|y_val:&FpGoldilocks| *y_val).collect();
    let trace_poly:DensePolynomial<FpGoldilocks> = lagrange_interpolation(&x, y);


    // Boundary constraint for first two and last 
    let b_poly_0:DensePolynomial<FpGoldilocks> = &trace_poly - get_fp_in_poly(FpGoldilocks::from(0)); // F(x)-0 = 0 at g^0
    let b_poly_1:DensePolynomial<FpGoldilocks> = &trace_poly - get_fp_in_poly(FpGoldilocks::from(1)); // F(x)-1 = 0 at g^1
    let b_poly_second_final:DensePolynomial<FpGoldilocks> = &trace_poly - get_fp_in_poly(FpGoldilocks::from(8)); // F(x)-8 = 0 at g^6 ( g^final-1)
    let b_poly_final:DensePolynomial<FpGoldilocks> = &trace_poly - get_fp_in_poly(FpGoldilocks::from(13)); // F(x)-13 = 0 at g^7 ( g^final)

    //Transition constraint
    let g_0:FpGoldilocks = roots_unity_T[0]; //g^0
    let g_1:FpGoldilocks = roots_unity_T[1]; //g^1
    let g_2:FpGoldilocks = roots_unity_T[2]; //g^2
    let g_second_final:FpGoldilocks = roots_unity_T[T-2];//g^6 (g^final-1)
    let g_final:FpGoldilocks = roots_unity_T[T-1]; //g^7 (g^final)

    let trace_poly_shifted_g_1:DensePolynomial<FpGoldilocks> = get_shifted_poly(&trace_poly,g_1); //f(gx)
    let trace_poly_shifted_g_2:DensePolynomial<FpGoldilocks> = get_shifted_poly(&trace_poly,g_2); //f(g^2 x)

    let transition_poly:DensePolynomial<FpGoldilocks> = trace_poly_shifted_g_2 - trace_poly_shifted_g_1 - trace_poly; // T(x) = f(g^2 x) - f(gx) - f(x)

    // Quotient polynomial
    let x_g_0:DensePolynomial<FpGoldilocks> = DensePolynomial::from_coefficients_vec(vec![-g_0,FpGoldilocks::from(1)]); // x-g^0
    let x_g_1:DensePolynomial<FpGoldilocks> = DensePolynomial::from_coefficients_vec(vec![-g_1,FpGoldilocks::from(1)]); // x-g^1
    let x_g_second_final:DensePolynomial<FpGoldilocks> = DensePolynomial::from_coefficients_vec(vec![-g_second_final,FpGoldilocks::from(1)]); // x-g^6 (g^final-1)
    let x_g_final:DensePolynomial<FpGoldilocks> = DensePolynomial::from_coefficients_vec(vec![-g_final,FpGoldilocks::from(1)]); // x-g^7 (g^final)

    let q_poly_0:DensePolynomial<FpGoldilocks> = b_poly_0/x_g_0; // f(x)-0 / (x-g^0) 
    let q_poly_1:DensePolynomial<FpGoldilocks> = b_poly_1/x_g_1; // f(x)-1 / (x-g^1)
    let q_poly_second_final:DensePolynomial<FpGoldilocks> = b_poly_second_final/&x_g_second_final; // f(x)-8 / (x-g^6) **(x-g^final-1)
    let q_poly_final:DensePolynomial<FpGoldilocks> = b_poly_final/&x_g_final; // f(x)-13 / (x-g^7) **(x-g^final)

    let x_n_poly:DensePolynomial<FpGoldilocks> = get_x_n_poly(T); // (x^n -1) Whole evaluation domain condensed
    let x_n_poly_trimmed:DensePolynomial<FpGoldilocks> = x_n_poly/(x_g_second_final*x_g_final); // (x^n -1)/ [(x-g^final-1) * (X-g^final)] (Removing last two from the roots)
    let t_q_poly:DensePolynomial<FpGoldilocks> = transition_poly/x_n_poly_trimmed; // Transition quotient polynomial

    //Fiat shamir for random challenge

    //Transcript (Public)
    let mut t_0:Vec<FpGoldilocks> = roots_unity_T;
    let mut t1:Vec<FpGoldilocks> = roots_unity_N.clone();
    t_0.append(&mut t1);
    let transcript:Vec<FpGoldilocks> = t_0;

    let (mut prover_state,[coset_fp,alpha0,alpha1,alpha2,alpha3,alpha4])= fiat_shamir_challenges_one(transcript,N);
    let lde_evaluation_domain:Vec<FpGoldilocks> = multiply_by_coset(&roots_unity_N,coset_fp); //Low degree extension of roots of unity domain

    //Composition polynomial
    let composition_poly = q_poly_0*alpha0 + q_poly_1*alpha1 + q_poly_second_final*alpha2 + q_poly_final*alpha3 + t_q_poly*alpha4;
    
    //Merkle commitment
    let RS_CODEWORDS:Vec<FpGoldilocks> = evaluate_poly_from_domain(&composition_poly,&lde_evaluation_domain); // Evaluation of polynomial over the extended domain (Reed solomon codewords)
    let RS_CODEWORDS_HASH:Vec<FpGoldilocks> = compute_hash_list(&RS_CODEWORDS);
    let trace_merkle_root:FpGoldilocks = commit(RS_CODEWORDS_HASH.clone());
    
    //Sample for linear combination in folded polynomial
    prover_state.add_scalars(&[trace_merkle_root]).expect("Fiat shamir error!! Scalar addition failed"); 
    let [r_challenge]: [FpGoldilocks; 1] = prover_state.challenge_scalars().expect("Fiat shamir error!! Challenge genration failed");  
    
    //Sample random index 'i' for query
    prover_state.add_scalars(&[r_challenge]).expect("Fiat shamir error!! Scalar addition failed");  
    let [index_challenge]: [FpGoldilocks; 1] = prover_state.challenge_scalars().expect("Fiat shamir error!! Challenge genration failed");  

    let mut unfolded_poly:DensePolynomial<FpGoldilocks> = composition_poly;
    let mut unfolded_evaluation_domain:Vec<FpGoldilocks> = lde_evaluation_domain;
    let mut unfolded_codewords:Vec<FpGoldilocks> = RS_CODEWORDS;
    let mut unfolded_codewords_hash:Vec<FpGoldilocks> = RS_CODEWORDS_HASH;
    let mut unfolded_merkle_root:FpGoldilocks = trace_merkle_root;
    let mut query_challenge:FpGoldilocks = index_challenge;
    let mut round:usize = 1;
    let mut proof:Vec<Vec<FpGoldilocks>> = vec![vec![trace_merkle_root]]; //(Initialized with merkle root), Per round [[root,authentication_paths]...]

    // FRI (Prover)
    while unfolded_evaluation_domain.len() > 1 {

        let coeff_list:&[FpGoldilocks] = unfolded_poly.coeffs();
        let (even_coeffs,odd_coeffs) = get_even_odd_coeff(&coeff_list.to_vec());

        let f_even_poly:DensePolynomial<FpGoldilocks> = DensePolynomial::from_coefficients_vec(even_coeffs);
        let f_odd_poly:DensePolynomial<FpGoldilocks> = DensePolynomial::from_coefficients_vec(odd_coeffs);
        let folded_poly:DensePolynomial<FpGoldilocks> = f_even_poly + f_odd_poly.mul(r_challenge);
        //Commit to folded evaluation domain
        let folded_domain:Vec<FpGoldilocks> = fold_domain(&unfolded_evaluation_domain);
        let folded_domain_len:usize = folded_domain.len();
        let folded_rs_codewords:Vec<FpGoldilocks> = evaluate_poly_from_domain(&folded_poly,&folded_domain); // Evaluation of polynomial over the extended domain (Reed solomon codewords)
        let folded_rs_codewords_hash:Vec<FpGoldilocks> = compute_hash_list(&folded_rs_codewords);
        let folded_root:FpGoldilocks =  commit(folded_rs_codewords_hash.clone());

        let query_index = get_bounded_index(query_challenge,folded_domain_len-1);

        // Verify merkle roots with authentication paths
        
        // For unfolded merkle root
        let authentication_paths_one:Vec<FpGoldilocks> = compute_sibling_values(query_index, unfolded_codewords_hash.clone());
        let authentication_paths_two:Vec<FpGoldilocks> = compute_sibling_values((unfolded_evaluation_domain.len()/2) + query_index, unfolded_codewords_hash.clone());
        let authentication_paths_three:Vec<FpGoldilocks> = compute_sibling_values(query_index, folded_rs_codewords_hash);

        //Add proof
        let mut proof_one:Vec<FpGoldilocks> = Vec::new();
        let mut proof_two:Vec<FpGoldilocks> = Vec::new();
        let mut proof_three:Vec<FpGoldilocks> = Vec::new();
        
        if round == 1{
            //Add proof 
            proof_one = merge_list(
                vec![
                    unfolded_merkle_root,
                    unfolded_codewords[query_index],
                    FpGoldilocks::from(authentication_paths_one.len() as u64)],
                &authentication_paths_one
            );
        }else{
            //Add proof 
            proof_one = merge_list(
                vec![
                    unfolded_codewords[query_index],
                    FpGoldilocks::from(authentication_paths_one.len() as u64)],
                &authentication_paths_one
            );
        }
        proof_two = merge_list(
            vec![
                unfolded_codewords[(unfolded_evaluation_domain.len()/2) + query_index],
                FpGoldilocks::from(authentication_paths_two.len() as u64)],
            &authentication_paths_two
        );

        proof_three = merge_list(
            vec![
                folded_root,
                folded_rs_codewords[query_index],
                FpGoldilocks::from(authentication_paths_three.len() as u64)],
            &authentication_paths_three
        );

        proof.push(proof_one);
        proof.push(proof_two);
        proof.push(proof_three);

        // //Verify commitments
        verify_commitment(// f(w^i)
            query_index,
            compute_hash_one(unfolded_codewords[query_index]),
            authentication_paths_one,
            unfolded_merkle_root
        ); 

        verify_commitment( // f(-w^i)
            (unfolded_evaluation_domain.len()/2) + query_index,
        compute_hash_one(unfolded_codewords[(unfolded_evaluation_domain.len()/2) + query_index]),
            authentication_paths_two,
            unfolded_merkle_root
        ); 

        //For folded merkle root
        verify_commitment( // f((-w^i))^2
            query_index,
        compute_hash_one(folded_rs_codewords[query_index]),
            authentication_paths_three,
            folded_root
        ); 

        // Other rounds
        if folded_domain_len != 1{
            query_challenge = add_sample_index_challenge(&mut prover_state,folded_root);

        }else if folded_domain_len == 1{ //Second last round
            //Push the constant polynomial 
            let t_hash = compute_hash_one(folded_poly.coeffs()[0]);
            proof.push(vec![t_hash]);
        }
        
        unfolded_codewords = evaluate_poly_from_domain(&folded_poly,&folded_domain); // Evaluation of polynomial over the extended domain (Reed solomon codewords)
        unfolded_codewords_hash = compute_hash_list(&unfolded_codewords);
        unfolded_merkle_root = commit(unfolded_codewords_hash.clone());

        unfolded_poly = folded_poly;
        unfolded_evaluation_domain = folded_domain;
        round = round + 1;
    }

    // Convert proof to string 
    let proof_string:String = concatenate_proof_string(proof);
    println!("Proof string: {:?}",proof_string);

}

