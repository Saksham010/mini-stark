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
use std::env;

use std::io::{Result,Read,Cursor};
// use ark_serialize::Write;

use std::ops::{Mul};

use base64::{engine::general_purpose, Engine as _}; // Import the Engine trait


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

fn verify_commitment(commit_index:usize, commit_val_hash:FpGoldilocks, authentication_paths:Vec<FpGoldilocks>,merkle_root:FpGoldilocks){

    // //Verifier opens proof at the value
    let is_valid_opening:bool = verify_opening(commit_index,commit_val_hash,&authentication_paths,&merkle_root);
    println!("Is valid opening: {:?}",is_valid_opening);
    assert_eq!(is_valid_opening,true);
}

//Generate roots of unity (2 Adic)
fn generate_evaluation_domain(size:usize)->Vec<FpGoldilocks>{
    println!("Size of evaluation domain: {:?}",size);
    let domain = Radix2EvaluationDomain::<FpGoldilocks>::new(size).expect("Evaluation domain generation failed!!");  
    let roots: Vec<FpGoldilocks> = domain.elements().collect(); 
    println!("Evaluation domain elements: {:?}",roots);
    roots[0..size].to_vec()
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
fn main(){
	//Read proof 
    let args: Vec<String> = env::args().collect();
    let proof_string = &args[1];
    let parsed_proof = parse_proof(&proof_string);
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
    let mut t1:Vec<FpGoldilocks> = roots_unity_N;
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
    
    // Generate challenge for composition
    prover_state.add_scalars(&[coset_fp]).expect("Fiat shamir error!! Scalar addition failed"); 
    let [alpha0,alpha1,alpha2,alpha3,alpha4]: [FpGoldilocks; 5] = prover_state.challenge_scalars().expect("Fiat shamir error!! Challenge genration failed");  


    //Sample for linear combination in folded polynomial
    prover_state.add_scalars(&[composition_merkle_root]).expect("Fiat shamir error!! Scalar addition failed"); 
    let [r_challenge]: [FpGoldilocks; 1] = prover_state.challenge_scalars().expect("Fiat shamir error!! Challenge genration failed");  
    
    //Sample random index 'i' for query
    prover_state.add_scalars(&[r_challenge]).expect("Fiat shamir error!! Scalar addition failed");  
    let [index_challenge]: [FpGoldilocks; 1] = prover_state.challenge_scalars().expect("Fiat shamir error!! Challenge genration failed");  

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
            // let unfolded_query_index_one = round_list[0][1];
            let unfolded_commit_value_one = round_list[0][1];
            let unfolded_authentication_path_one = &round_list[0][3..];
            
            // let unfolded_query_index_two = round_list[1][0];
            let unfolded_commit_value_two = round_list[1][0];
            let unfolded_authentication_path_two = &round_list[1][2..];
            
            let folded_root_vr = round_list[2][0];
            // let folded_query_index = round_list[2][1];
            let folded_commit_value = round_list[2][1];
            let folded_authentication_path = &round_list[2][3..];
            
            let folded_query_index = get_bounded_index(sample_query_index,(unfolded_domain_size/2)-1);

            verify_commitment(folded_query_index, unfolded_commit_value_one, unfolded_authentication_path_one.to_vec(), unfolded_root_vr);
            verify_commitment((N/2)+folded_query_index, unfolded_commit_value_two, unfolded_authentication_path_two.to_vec(), unfolded_root_vr);
            verify_commitment(folded_query_index, folded_commit_value, folded_authentication_path.to_vec(), folded_root_vr);

            //Collinearity test
            // A = (w^i,f(w^i)), B = (-w^i,f(w^N/2+i)), C = (r, folded_f((w^i))^2)
            // let x_list = vec![
            //     unfolded_evaluation_domain[folded_query_index],
            //     unfolded_evaluation_domain[(unfolded_domain_size/2) + folded_query_index],
            // ];
            // let y_list = vec![
            //     unfolded_codewords[folded_query_index],
            //     unfolded_codewords[(unfolded_domain_size/2) + folded_query_index],
            // ];

            // let a_b_poly:DensePolynomial<FpGoldilocks> = lagrange_interpolation(&x_list,y_list); //Intepolate A,B 
            // let a_b_poly_eval = a_b_poly.evaluate(&r_challenge); //Colinearity test
            // assert_eq!(a_b_poly_eval,folded_rs_codewords[query_index]); // eval ===? f(w^i)^2

            //Add scalar for new challenge
            prover_state.add_scalars(&[folded_root_vr]).expect("Fiat shamir error!! Scalar addition failed");  
            let [sample_index_challenge]: [FpGoldilocks; 1] = prover_state.challenge_scalars().expect("Fiat shamir error!! Challenge genration failed");  
            sample_query_index = sample_index_challenge;

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

            verify_commitment(folded_query_index, unfolded_commit_value_one, unfolded_authentication_path_one.to_vec(), unfolded_root_vr);
            verify_commitment((unfolded_domain_size/2) + folded_query_index, unfolded_commit_value_two, unfolded_authentication_path_two.to_vec(), unfolded_root_vr);
            verify_commitment(folded_query_index, folded_commit_value, folded_authentication_path.to_vec(), folded_root_vr);

            if unfolded_domain_size > 2{
                //Next round will have a constant so no sampling is required
                prover_state.add_scalars(&[folded_root_vr]).expect("Fiat shamir error!! Scalar addition failed");  
                let [sample_index_challenge]: [FpGoldilocks; 1] = prover_state.challenge_scalars().expect("Fiat shamir error!! Challenge genration failed");  
                sample_query_index = sample_index_challenge;

            }

            //Update prev root
            prev_round_root = folded_root_vr;
        }
        unfolded_domain_size = unfolded_domain_size/2;
    }

}