mod fields;
mod merkle;
use crate::merkle::merkle::verify_opening;
use ark_poly::{EvaluationDomain,Radix2EvaluationDomain,univariate::DensePolynomial,DenseUVPolynomial}; 
use spongefish::codecs::arkworks_algebra::*;  
use spongefish::{DomainSeparator,DefaultHash};
use ark_serialize::CanonicalSerialize;
use ark_serialize::CanonicalDeserialize;
use std::io::{Read,Cursor};

use base64::{engine::general_purpose, Engine as _}; // Import the Engine trait
pub use crate::fields::goldilocks::FpGoldilocks;

//Convert list in fp_list
pub fn get_fp_from_list(u64_list:&Vec<u64>)->Vec<FpGoldilocks>{
    let mut fp_list:Vec<FpGoldilocks> = Vec::new();
    for val in u64_list{
        fp_list.push(FpGoldilocks::from(*val));
    }
    fp_list
}

//Generate roots of unity (2 Adic)
pub fn generate_evaluation_domain(size:usize)->Vec<FpGoldilocks>{
    let domain = Radix2EvaluationDomain::<FpGoldilocks>::new(size).expect("Evaluation domain generation failed!!");  
    let roots: Vec<FpGoldilocks> = domain.elements().collect(); 
    roots[0..size].to_vec()
}

//Get dense uv polynomial from vec
pub fn get_dense_uv_poly(coeff:Vec<FpGoldilocks>)->DensePolynomial<FpGoldilocks>{
    DensePolynomial::from_coefficients_vec(coeff)
}

//Lagrange interpolation
pub fn lagrange_interpolation(x:&Vec<FpGoldilocks>,y:Vec<FpGoldilocks>)->DensePolynomial<FpGoldilocks>{
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

    interpolated_poly

}

// Multiply each element of vector by scalar
pub fn multiply_by_coset(x_list:&Vec<FpGoldilocks>,coset:FpGoldilocks)->Vec<FpGoldilocks>{
    let mut coset_list:Vec<FpGoldilocks> = Vec::new();
    for val in x_list{
        coset_list.push(coset*(*val));
    }
    coset_list

}

//Get denspolynomial from fp
pub fn get_fp_in_poly(fp_val:FpGoldilocks)->DensePolynomial<FpGoldilocks>{
    DensePolynomial::from_coefficients_vec(vec![FpGoldilocks::from(fp_val)])
}

//Get powers of value
pub fn get_power_fp(g:FpGoldilocks,times:usize)->FpGoldilocks{
    let mut g_f:FpGoldilocks = FpGoldilocks::from(1);
    for _ in 0..times{
        g_f = g_f*g;
    }
    g_f
}

//Get polynomial shifted by value
pub fn get_shifted_poly(o_poly:&DensePolynomial<FpGoldilocks>,g_val:FpGoldilocks)->DensePolynomial<FpGoldilocks>{
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
pub fn get_x_n_poly(n:usize)->DensePolynomial<FpGoldilocks>{    
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
pub fn evaluate_poly(p:&DensePolynomial<FpGoldilocks>,eval:FpGoldilocks) -> FpGoldilocks{
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
pub fn evaluate_poly_from_domain(p:&DensePolynomial<FpGoldilocks>,evaluation_domain:&Vec<FpGoldilocks>)->Vec<FpGoldilocks>{
    let mut RS_CODEWORD:Vec<FpGoldilocks> = Vec::new();
    for eval in evaluation_domain{
        RS_CODEWORD.push(evaluate_poly(p, *eval));
    }
    RS_CODEWORD
}

//Check if value exist in a list
pub fn check_if_exist(v_list:&Vec<FpGoldilocks>,val:FpGoldilocks)->bool{
    for v in v_list{
        if *v == val{
            return true;
        }
    }
    false
}

//Folded evaluation domain
pub fn fold_domain(domain:&Vec<FpGoldilocks>)->Vec<FpGoldilocks>{
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
pub fn get_bounded_index(index:FpGoldilocks, bound:usize)->usize{
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

pub fn verify_commitment(commit_index:usize, commit_val_hash:FpGoldilocks, authentication_paths:Vec<FpGoldilocks>,merkle_root:FpGoldilocks){

    // //Verifier opens proof at the value
    let is_valid_opening:bool = verify_opening(commit_index,commit_val_hash,&authentication_paths,&merkle_root);
    assert_eq!(is_valid_opening,true);
}

// Returns merge list
pub fn merge_list(vec_one:Vec<FpGoldilocks>,vec_two:&Vec<FpGoldilocks>)->Vec<FpGoldilocks>{
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
pub fn concatenate_proof_string(proof:Vec<Vec<FpGoldilocks>>)->String{
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

//Return prover state
pub fn initialize_domain_separator(transcript_len:usize,N:usize) -> ProverState{
    let mut domsep = <DomainSeparator<DefaultHash> as FieldDomainSeparator<FpGoldilocks>>::add_scalars(
        DomainSeparator::<DefaultHash>::new("zk-stark"),
        transcript_len,
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

    let prover_state = domsep.to_prover_state();
    prover_state
}

//Add and sample index challege
pub fn add_sample_index_challenge(prover_state:&mut ProverState,folded_root_vr:FpGoldilocks)->FpGoldilocks{
    prover_state.add_scalars(&[folded_root_vr]).expect("Fiat shamir error!! Scalar addition failed");  
    let [sample_index_challenge]: [FpGoldilocks; 1] = prover_state.challenge_scalars().expect("Fiat shamir error!! Challenge genration failed");  
    sample_index_challenge
}