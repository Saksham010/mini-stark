mod fields;
mod merkle;
use crate::fields::goldilocks::FpGoldilocks;
use crate::merkle::merkle::{commit,compute_hash_list,compute_hash_one,compute_sibling_values,verify_opening};
use ark_poly::Polynomial;
use ark_poly::{EvaluationDomain,Radix2EvaluationDomain,univariate::DensePolynomial,DenseUVPolynomial}; 
use ark_std::rand::{thread_rng};
use ark_ff::{AdditiveGroup, UniformRand,PrimeField,BigInteger};
use spongefish::codecs::arkworks_algebra::*;  
use spongefish::{DomainSeparator,DefaultHash};
use ark_serialize::CanonicalSerialize;
use ark_serialize::CanonicalDeserialize;

use std::io::{Result,Read,Cursor};
// use ark_serialize::Write;

use std::ops::{Mul};

use base64::{engine::general_purpose, Engine as _}; // Import the Engine trait


//Convert list in fp_list
fn get_fp_from_list(u64_list:&Vec<u64>)->Vec<FpGoldilocks>{
    let mut fp_list:Vec<FpGoldilocks> = Vec::new();
    for val in u64_list{
        fp_list.push(FpGoldilocks::from(*val));
    }
    fp_list
}

//Generate roots of unity (2 Adic)
fn generate_evaluation_domain(size:usize)->Vec<FpGoldilocks>{
    println!("Size of evaluation domain: {:?}",size);
    let domain = Radix2EvaluationDomain::<FpGoldilocks>::new(size).expect("Evaluation domain generation failed!!");  
    let roots: Vec<FpGoldilocks> = domain.elements().collect(); 
    println!("Evaluation domain elements: {:?}",roots);
    roots[0..size].to_vec()
}

//Get dense uv polynomial from vec
fn get_dense_uv_poly(coeff:Vec<FpGoldilocks>)->DensePolynomial<FpGoldilocks>{
    DensePolynomial::from_coefficients_vec(coeff)
}

//Lagrange interpolation
fn lagrange_interpolation(x:&Vec<FpGoldilocks>,y:Vec<FpGoldilocks>)->DensePolynomial<FpGoldilocks>{
    if x.len() != y.len(){
        panic!("Interpolation error: X,Y length is not equal!!");
    }

    let mut interpolated_poly:DensePolynomial<FpGoldilocks> = get_dense_uv_poly(vec![FpGoldilocks::from(0)]);

    for i in 0..x.len(){    
        let mut li_x:DensePolynomial<FpGoldilocks> = DensePolynomial::from_coefficients_vec(vec![FpGoldilocks::from(1)]);
        for k in x {
            // k != wi 
            if *k != x[i]{
                let t_li:DensePolynomial<FpGoldilocks> = (get_dense_uv_poly(vec![FpGoldilocks::from(0),FpGoldilocks::from(1)]) - get_dense_uv_poly(vec![*k]))/get_dense_uv_poly(vec![x[i]-*k]); 
                li_x = li_x * t_li;
            }
            
        }
        interpolated_poly = interpolated_poly + get_dense_uv_poly(vec![y[i]]) * li_x;

    }
    println!("Interpolated polynomial: {:?}", &interpolated_poly);

    interpolated_poly

}

// Multiply each element of vector by scalar
fn multiply_by_coset(x_list:Vec<FpGoldilocks>,coset:FpGoldilocks)->Vec<FpGoldilocks>{
    let mut coset_list:Vec<FpGoldilocks> = Vec::new();
    for val in x_list{
        coset_list.push(coset*val);
    }
    coset_list

}

//Get denspolynomial from fp
fn get_fp_in_poly(fp_val:FpGoldilocks)->DensePolynomial<FpGoldilocks>{
    DensePolynomial::from_coefficients_vec(vec![FpGoldilocks::from(fp_val)])
}

//Get powers of value
fn get_power_fp(g:FpGoldilocks,times:usize)->FpGoldilocks{
    let mut g_f:FpGoldilocks = FpGoldilocks::from(1);
    for _ in 0..times{
        g_f = g_f*g;
    }
    g_f
}

//Get polynomial shifted by value
fn get_shifted_poly(o_poly:&DensePolynomial<FpGoldilocks>,g_val:FpGoldilocks)->DensePolynomial<FpGoldilocks>{
    let mut _coeff_list:&[FpGoldilocks] = o_poly.coeffs();
    let mut shifted_coeff_list:Vec<FpGoldilocks> = Vec::new();

    for (index,val) in _coeff_list.iter().enumerate(){
        if index > 0 {
            let g_i:FpGoldilocks = get_power_fp(g_val, index);
            let shifted_coeff:FpGoldilocks = *val * g_i;
            shifted_coeff_list.push(shifted_coeff);

        }else{
            // Index == 0 for coeff with x^0
            shifted_coeff_list.push(*val);
        }
    }   

    DensePolynomial::from_coefficients_vec(shifted_coeff_list)
}

// Get x^n -1 polynomial
fn get_x_n_poly(n:usize)->DensePolynomial<FpGoldilocks>{    
    let mut coeff_list:Vec<FpGoldilocks> = Vec::new();
    for  i in 0..n{
        
        if i == n-1{
            coeff_list.push(FpGoldilocks::from(0)); // 0 for n-1th power
            coeff_list.push(FpGoldilocks::from(1)); // 1 for nth power
        }else if i == 0{
            coeff_list.push(FpGoldilocks::from(-1));
        }else{
            coeff_list.push(FpGoldilocks::from(0));
        }

    }

    DensePolynomial::from_coefficients_vec(coeff_list)
}


// Evaluate polynomial
fn evaluate_poly(p:&DensePolynomial<FpGoldilocks>,eval:FpGoldilocks) -> FpGoldilocks{
    //gw^0
    let coeffs:&[FpGoldilocks] = p.coeffs();
    let mut sum:FpGoldilocks = FpGoldilocks::from(0);
    let mut power:usize = 0;
    for coeff in coeffs {
        sum = sum + *coeff * get_power_fp(eval,power);
        power = power + 1;
    }
    sum
}

// Get evaluations of polynomial over a domain
fn evaluate_poly_from_domain(p:&DensePolynomial<FpGoldilocks>,evaluation_domain:Vec<FpGoldilocks>)->Vec<FpGoldilocks>{
    let mut RS_CODEWORD:Vec<FpGoldilocks> = Vec::new();
    for eval in evaluation_domain{
        RS_CODEWORD.push(evaluate_poly(p, eval));
    }
    RS_CODEWORD
}

//Check if value exist in a list
fn check_if_exist(v_list:&Vec<FpGoldilocks>,val:FpGoldilocks)->bool{
    for v in v_list{
        if *v == val{
            return true;
        }
    }
    false
}

//Folded evaluation domain
fn fold_domain(domain:&Vec<FpGoldilocks>)->Vec<FpGoldilocks>{
    let mut folded_domain:Vec<FpGoldilocks> = Vec::new();

    for d in domain{
        let d_squared:FpGoldilocks = get_power_fp(*d, 2);
        let does_exist:bool = check_if_exist(&folded_domain, d_squared);
        if !does_exist{
            folded_domain.push(d_squared);
        } 
    }   

    folded_domain
}

// Get index within a bound
fn get_bounded_index(index:FpGoldilocks, bound:usize)->usize{
    if bound == 0{
        return 0;
    }
    let mut bytes = Vec::new();
    index.serialize_compressed(&mut bytes).unwrap(); // deterministic serialization
    let mut temp_index:usize = bytes[0] as usize;
    while temp_index > bound {
        temp_index = temp_index%bound;
    }

    temp_index
}

fn verify_commitment(commit_index:usize, commit_val_hash:FpGoldilocks, authentication_paths:Vec<FpGoldilocks>,merkle_root:FpGoldilocks){

    // //Verifier opens proof at the value
    let is_valid_opening:bool = verify_opening(commit_index,commit_val_hash,&authentication_paths,&merkle_root);
    println!("Is valid opening: {:?}",is_valid_opening);
    assert_eq!(is_valid_opening,true);
}

// Returns merge list
fn merge_list(vec_one:Vec<FpGoldilocks>,vec_two:&Vec<FpGoldilocks>)->Vec<FpGoldilocks>{
    let mut merged_list:Vec<FpGoldilocks> = vec_one;
    for value in vec_two{
        merged_list.push(*value);
    }
    merged_list
}

//Generate proof string
fn generate_proof_string(proof:&Vec<FpGoldilocks>)->String{
    let mut proof_binary:Vec<u8> = Vec::new();
    for p in proof{
        let mut serialized_data = Vec::new();
        let _ = p.serialize_uncompressed(&mut serialized_data);
        let data_len: Vec<u8> = vec![serialized_data.len() as u8];
        proof_binary.extend(data_len);
        proof_binary.extend(serialized_data); 
    }

    let proof_string = general_purpose::STANDARD.encode(proof_binary.clone());
    proof_string
    
}

//Concatenate proof string
fn concatenate_proof_string(proof:Vec<Vec<FpGoldilocks>>)->String{
    let mut proof_string = String::from("");
    for p in proof {
        let proof_s = generate_proof_string(&p);
        proof_string = proof_string + &proof_s;        
    }
    proof_string
}



// Parse proof string
pub fn parse_proof(proof:&str) -> Vec<FpGoldilocks>{
    let proof_binary:Vec<u8> =  general_purpose::STANDARD.decode(proof).expect("Invalid proof !!");
    let mut cursor = Cursor::new(&proof_binary[..]);
    let mut deserialized_proof:Vec<FpGoldilocks> = Vec::new();

    //Deserialize proof elements
    while (cursor.position() as usize) < cursor.get_ref().len(){ 
    
        //Read the length
        let mut element_len =[0u8];
        cursor.read_exact(&mut element_len).expect("Invalid proof !!"); // Read element length
        let mut element: Vec<u8> = vec![0u8;element_len[0] as usize];
        cursor.read_exact(&mut element).expect("Invalid proof !!"); //Read element

        //Deseralize
        let mut cursor_element = Cursor::new(element);
        let deserialized_element:FpGoldilocks = FpGoldilocks::deserialize_uncompressed(&mut cursor_element).expect("Invalid proof !!");
        deserialized_proof.push(deserialized_element); //Push the element

    }
    deserialized_proof
}


//Convert FpGoldilocks to usize
fn unsafe_goldilocks_to_usize(x: FpGoldilocks) -> usize {
    x.into_bigint().0[0] as usize
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
        // FpGoldilocks::from(21),
        // FpGoldilocks::from(34),
        // FpGoldilocks::from(55),
        // FpGoldilocks::from(89)
    ];

    let blowupfactor:usize = 4; // Larger the blowupfactor better the soundness
    let T = execution_trace.len(); //Trace length (dimension k in RS code)
    let N = blowupfactor * T; //Size for extension domain

    //Evaluation domain (Roots of unity) of size
    let roots_unity_T:Vec<FpGoldilocks> = generate_evaluation_domain(T);

    //Low degree extension
    let roots_unity_N:Vec<FpGoldilocks> = generate_evaluation_domain(N);
    let mut rng = thread_rng();
    // let coset_fp:FpGoldilocks = FpGoldilocks::rand(&mut rng);
    // let lde_evaluation_domain:Vec<FpGoldilocks> = multiply_by_coset(roots_unity_N.clone(),coset_fp); //Low degree extension of roots of unity domain

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


    let mut domsep = <DomainSeparator<DefaultHash> as FieldDomainSeparator<FpGoldilocks>>::add_scalars(
        DomainSeparator::<DefaultHash>::new("zk-stark"),
        transcript.len(),
        "full_transcript",
    );

    domsep = <DomainSeparator<DefaultHash> as FieldDomainSeparator<FpGoldilocks>>::challenge_scalars(
        domsep,
        1,               // number of scalars for the challenge
        "Coset challenge",         // label for the challenge
    );

    domsep = <DomainSeparator<DefaultHash> as FieldDomainSeparator<FpGoldilocks>>::add_scalars(
        domsep,
        1,
        "Coset transcript",
    );

    domsep = <DomainSeparator<DefaultHash> as FieldDomainSeparator<FpGoldilocks>>::challenge_scalars(
        domsep,
        5,               // number of scalars for the challenge
        "composition challenge",         // label for the challenge
    );

    domsep = <DomainSeparator<DefaultHash> as FieldDomainSeparator<FpGoldilocks>>::add_scalars(
        domsep,
        1,
        "merkle root CP",
    );

    domsep = <DomainSeparator<DefaultHash> as FieldDomainSeparator<FpGoldilocks>>::challenge_scalars(
        domsep,
        1,               // number of scalars for the challenge
        "Folded challenge",         // label for the challenge
    );

    // Define strucutre for all rounds of FRI
    let mut simulated_domain_size:usize = N; 
    while simulated_domain_size > 1 {
        println!("SIMULATED RUNTIME: {:?}", simulated_domain_size);

        let round_add_label = String::from("Folded root add round  ") + &simulated_domain_size.to_string();
        let round_challenge_label = String::from("Folded root challenge round: ") + &simulated_domain_size.to_string();

        domsep = <DomainSeparator<DefaultHash> as FieldDomainSeparator<FpGoldilocks>>::add_scalars(
        domsep,
        1,
        &round_add_label,
        );

        domsep = <DomainSeparator<DefaultHash> as FieldDomainSeparator<FpGoldilocks>>::challenge_scalars(
            domsep,
            1,               // number of scalars for the challenge
            &round_challenge_label,         // label for the challenge
        );
        simulated_domain_size = simulated_domain_size/2;
    }

    let mut prover_state = domsep.to_prover_state();

    // Add transcript
    prover_state.add_scalars(&transcript).expect("Fiat shamir error!! Scalar addition failed");  
    let [coset_fp]: [FpGoldilocks; 1] = prover_state.challenge_scalars().expect("Fiat shamir error!! Challenge genration failed");  
    let lde_evaluation_domain:Vec<FpGoldilocks> = multiply_by_coset(roots_unity_N.clone(),coset_fp); //Low degree extension of roots of unity domain
  
    // Generate challenge for composition
    prover_state.add_scalars(&[coset_fp]).expect("Fiat shamir error!! Scalar addition failed");  
    let [alpha0,alpha1,alpha2,alpha3,alpha4]: [FpGoldilocks; 5] = prover_state.challenge_scalars().expect("Fiat shamir error!! Challenge genration failed");  

    //Composition polynomial
    let composition_poly = q_poly_0*alpha0 + q_poly_1*alpha1 + q_poly_second_final*alpha2 + q_poly_final*alpha3 + t_q_poly*alpha4;
    
    
    // FRI (Prover)
    //Merkle commitment
    let RS_CODEWORDS:Vec<FpGoldilocks> = evaluate_poly_from_domain(&composition_poly,lde_evaluation_domain.clone()); // Evaluation of polynomial over the extended domain (Reed solomon codewords)
    let RS_CODEWORDS_HASH:Vec<FpGoldilocks> = compute_hash_list(&RS_CODEWORDS);
    let trace_merkle_root:FpGoldilocks = commit(RS_CODEWORDS_HASH.clone());
    
    //Sample for linear combination in folded polynomial
    prover_state.add_scalars(&[trace_merkle_root]).expect("Fiat shamir error!! Scalar addition failed"); 
    let [r_challenge]: [FpGoldilocks; 1] = prover_state.challenge_scalars().expect("Fiat shamir error!! Challenge genration failed");  
    
    //Sample random index 'i' for query
    prover_state.add_scalars(&[r_challenge]).expect("Fiat shamir error!! Scalar addition failed");  
    let [index_challenge]: [FpGoldilocks; 1] = prover_state.challenge_scalars().expect("Fiat shamir error!! Challenge genration failed");  
    // let sample_index:usize = get_bounded_index(index_challenge,lde_evaluation_domain.len());

    let mut unfolded_poly:DensePolynomial<FpGoldilocks> = composition_poly;
    let mut unfolded_evaluation_domain:Vec<FpGoldilocks> = lde_evaluation_domain;
    let mut unfolded_codewords:Vec<FpGoldilocks> = RS_CODEWORDS;
    let mut unfolded_codewords_hash:Vec<FpGoldilocks> = RS_CODEWORDS_HASH;
    let mut unfolded_merkle_root:FpGoldilocks = trace_merkle_root;
    let mut query_challenge:FpGoldilocks = index_challenge;
    let mut round:usize = 1;
    let mut proof:Vec<Vec<FpGoldilocks>> = vec![vec![trace_merkle_root]]; //(Initialized with merkle root), Per round [[root,authentication_paths]...]

    println!("Index challenge: {}",index_challenge);

    while unfolded_evaluation_domain.len() > 1 {
        println!("ROUND: {:?}",round);
        println!("ROUND DOMAIN SIZE: {:?}",unfolded_evaluation_domain.len());

        let coeff_list:&[FpGoldilocks] = unfolded_poly.coeffs();
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

        let f_even_poly:DensePolynomial<FpGoldilocks> = DensePolynomial::from_coefficients_vec(even_coeffs);
        let f_odd_poly:DensePolynomial<FpGoldilocks> = DensePolynomial::from_coefficients_vec(odd_coeffs);
        let folded_poly:DensePolynomial<FpGoldilocks> = f_even_poly + f_odd_poly.mul(r_challenge);
        //Commit to folded evaluation domain
        let folded_domain:Vec<FpGoldilocks> = fold_domain(&unfolded_evaluation_domain);
        let folded_domain_len:usize = folded_domain.len();
        let folded_rs_codewords:Vec<FpGoldilocks> = evaluate_poly_from_domain(&folded_poly,folded_domain.clone()); // Evaluation of polynomial over the extended domain (Reed solomon codewords)
        let folded_rs_codewords_hash:Vec<FpGoldilocks> = compute_hash_list(&folded_rs_codewords);
        let folded_root:FpGoldilocks =  commit(folded_rs_codewords_hash.clone());

        let query_index = get_bounded_index(query_challenge,folded_domain_len-1);
        println!("Query index in usize: {}",query_index);

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
                    // FpGoldilocks::from(query_index as u64),
                    compute_hash_one(unfolded_codewords[query_index]),
                    FpGoldilocks::from(authentication_paths_one.len() as u64)],
                &authentication_paths_one
            );
            proof_two = merge_list(
                vec![
                    // FpGoldilocks::from(((unfolded_evaluation_domain.len()/2) + query_index) as u64),
                    compute_hash_one(unfolded_codewords[(unfolded_evaluation_domain.len()/2) + query_index]),
                    FpGoldilocks::from(authentication_paths_two.len() as u64)],
                &authentication_paths_two
            );
            proof_three = merge_list(
                vec![
                    folded_root,
                    // FpGoldilocks::from(query_index as u64),
                    compute_hash_one(folded_rs_codewords[query_index]),
                    FpGoldilocks::from(authentication_paths_three.len() as u64)],
                &authentication_paths_three
            );
        }else{
            //Add proof 
            proof_one = merge_list(
                vec![
                    // FpGoldilocks::from(query_index as u64),
                    compute_hash_one(unfolded_codewords[query_index]),
                    FpGoldilocks::from(authentication_paths_one.len() as u64)],
                &authentication_paths_one
            );
            proof_two = merge_list(
                vec![
                    // FpGoldilocks::from(((unfolded_evaluation_domain.len()/2) + query_index) as u64),
                    compute_hash_one(unfolded_codewords[(unfolded_evaluation_domain.len()/2) + query_index]),
                    FpGoldilocks::from(authentication_paths_two.len() as u64)],
                &authentication_paths_two
            );
            proof_three = merge_list(
                vec![
                    folded_root,
                    // FpGoldilocks::from(query_index as u64),
                    compute_hash_one(folded_rs_codewords[query_index]),
                    FpGoldilocks::from(authentication_paths_three.len() as u64)],
                &authentication_paths_three
            );
        }
        proof.push(proof_one);
        proof.push(proof_two);
        proof.push(proof_three);

        //Verify commitments
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

        //Collinearity test
        // A = (w^i,f(w^i)), B = (-w^i,f(w^N/2+i)), C = (r, folded_f((w^i))^2)
        let x_list = vec![
            unfolded_evaluation_domain[query_index],
            unfolded_evaluation_domain[(unfolded_evaluation_domain.len()/2) + query_index],
        ];
        let y_list = vec![
            unfolded_codewords[query_index],
            unfolded_codewords[(unfolded_evaluation_domain.len()/2) + query_index],
        ];

        let a_b_poly:DensePolynomial<FpGoldilocks> = lagrange_interpolation(&x_list,y_list); //Intepolate A,B 
        let a_b_poly_eval = a_b_poly.evaluate(&r_challenge); //Colinearity test
        assert_eq!(a_b_poly_eval,folded_rs_codewords[query_index]); // eval ===? f(w^i)^2

        // Other rounds
        if folded_domain_len != 1{
            prover_state.add_scalars(&[folded_root]).expect("Fiat shamir error!! Scalar addition failed");  
            let [sample_index_challenge]: [FpGoldilocks; 1] = prover_state.challenge_scalars().expect("Fiat shamir error!! Challenge genration failed");  
            query_challenge = sample_index_challenge;

        }else if folded_domain_len == 1{ //Second last round
            //Push the constant polynomial 
            let t_hash = compute_hash_one(folded_poly.coeffs()[0]);
            proof.push(vec![t_hash]);
        }
        
        unfolded_codewords = evaluate_poly_from_domain(&folded_poly,folded_domain.clone()); // Evaluation of polynomial over the extended domain (Reed solomon codewords)
        unfolded_codewords_hash = compute_hash_list(&unfolded_codewords);
        unfolded_merkle_root = commit(unfolded_codewords_hash.clone());

        unfolded_poly = folded_poly;
        unfolded_evaluation_domain = folded_domain;
        round = round + 1;
    }

    println!("Proof element: {:?}",proof);
    println!("-------------------------------------------");
    // Convert proof to string 
    let proof_string:String = concatenate_proof_string(proof);
    println!("Proof string: {:?}",proof_string);

    //Verifier 

    // let proof_elements_vr = parse_proof(&proof_string);
    // // println!("Parsed proof string: {:?}",proof_elements_vr);

    // let mut temp_proof_list:Vec<FpGoldilocks> = Vec::new();
    // let mut proof_list_vr:Vec<Vec<FpGoldilocks>> = Vec::new();
    // let mut proof_list_round_vr:Vec<Vec<Vec<FpGoldilocks>>> = Vec::new(); // Roundwise proof elements
    // let mut auth_path_len_index:usize = 2; //[Root(0),commitval(1),authpathlen(2)] (Initialize)
    // let mut split_index:usize = 999;

    // for index in 0..proof_elements_vr.len(){
    //     //Constant value in last 
    //     if index+1 == proof_elements_vr.len(){
    //         proof_list_round_vr.push(vec![vec![proof_elements_vr[index]]]);
    //         break;
    //     }

    //     //First proof format : [Root,index,authpathlen,authpaths]
    //     if index == auth_path_len_index {
    //         let auth_path_len = proof_elements_vr[index];

    //         split_index = auth_path_len_index + unsafe_goldilocks_to_usize(auth_path_len);
            
    //         //Update authpathlen index
    //         if proof_list_vr.len() % 2 == 0{ //List is even then folded round left

    //             auth_path_len_index = split_index+2; 
    //         }else{//Odd
    //             auth_path_len_index = split_index+3;
    //         }
    //     }
    //     temp_proof_list.push(proof_elements_vr[index]);

    //     //List split per part of a round
    //     if index == split_index{
    //         proof_list_vr.push(temp_proof_list);
    //         temp_proof_list = vec![]; //Empty list

    //         //If round completed
    //         if proof_list_vr.len() == 3{
    //             //Push to final 
    //             proof_list_round_vr.push(proof_list_vr);
    //             //Empty the list
    //             proof_list_vr = vec![];
    //         }

    //     }        
    // }
    // println!("Proof by round : {:?}",proof_list_round_vr);

    // //Round by round FRI verification
    // let mut prev_round_root:FpGoldilocks = FpGoldilocks::from(0);
    // for (round,round_list) in proof_list_round_vr.iter().enumerate(){
    //     if round == 0{ // First round
    //         let unfolded_root_vr = round_list[0][0];
    //         // let unfolded_query_index_one = round_list[0][1];
    //         let unfolded_commit_value_one = round_list[0][1];
    //         let unfolded_authentication_path_one = &round_list[0][3..];
    //         verify_commitment(unsafe_goldilocks_to_usize(unfolded_query_index_one), unfolded_commit_value_one, unfolded_authentication_path_one.to_vec(), unfolded_root_vr);

    //         // let unfolded_query_index_two = round_list[1][0];
    //         let unfolded_commit_value_two = round_list[1][0];
    //         let unfolded_authentication_path_two = &round_list[1][2..];
    //         verify_commitment(unsafe_goldilocks_to_usize(unfolded_query_index_two), unfolded_commit_value_two, unfolded_authentication_path_two.to_vec(), unfolded_root_vr);

    //         let folded_root_vr = round_list[2][0];
    //         // let folded_query_index = round_list[2][1];
    //         let folded_commit_value = round_list[2][1];
    //         let folded_authentication_path = &round_list[2][3..];
    //         verify_commitment(unsafe_goldilocks_to_usize(folded_query_index), folded_commit_value, folded_authentication_path.to_vec(), folded_root_vr);

    //         //Update previous root
    //         prev_round_root = folded_root_vr;
    //     }else if round+1 == proof_list_round_vr.len(){//Last round
    //         continue;

    //     }else{
    //         //Other rounds
    //         let unfolded_root_vr = prev_round_root;
    //         // let unfolded_query_index_one = round_list[0][0];
    //         let unfolded_commit_value_one = round_list[0][0];
    //         let unfolded_authentication_path_one = &round_list[0][2..];
    //         verify_commitment(unsafe_goldilocks_to_usize(unfolded_query_index_one), unfolded_commit_value_one, unfolded_authentication_path_one.to_vec(), unfolded_root_vr);

    //         // let unfolded_query_index_two = round_list[1][0];
    //         let unfolded_commit_value_two = round_list[1][0];
    //         let unfolded_authentication_path_two = &round_list[1][2..];
    //         verify_commitment(unsafe_goldilocks_to_usize(unfolded_query_index_two), unfolded_commit_value_two, unfolded_authentication_path_two.to_vec(), unfolded_root_vr);

    //         let folded_root_vr = round_list[2][0];
    //         // let folded_query_index = round_list[2][1];
    //         let folded_commit_value = round_list[2][1];
    //         let folded_authentication_path = &round_list[2][3..];
    //         verify_commitment(unsafe_goldilocks_to_usize(folded_query_index), folded_commit_value, folded_authentication_path.to_vec(), folded_root_vr);

    //         //Update prev root
    //         prev_round_root = folded_root_vr;
    //     }
    // }
}

