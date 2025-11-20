mod fields;
mod merkle;
use crate::fields::goldilocks::FpGoldilocks;
use crate::merkle::merkle::commit;
use ark_poly::Polynomial;
use ark_poly::{EvaluationDomain,Radix2EvaluationDomain,univariate::DensePolynomial,DenseUVPolynomial}; 
use ark_std::rand::{thread_rng};
use ark_ff::{AdditiveGroup, UniformRand,PrimeField,BigInteger};
use spongefish::codecs::arkworks_algebra::*;  
use spongefish::{DomainSeparator,DefaultHash};
use ark_serialize::CanonicalSerialize;


use std::ops::{Mul};


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
    let mut bytes = Vec::new();
    index.serialize_compressed(&mut bytes).unwrap(); // deterministic serialization
    let mut temp_index:usize = bytes[0] as usize;
    while temp_index > bound {
        temp_index = temp_index/bound;
    }
    temp_index
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
    let coset_fp:FpGoldilocks = FpGoldilocks::rand(&mut rng);
    let lde_evaluation_domain:Vec<FpGoldilocks> = multiply_by_coset(roots_unity_N.clone(),coset_fp); //Low degree extension of roots of unity domain

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
        5,               // number of scalars for the challenge
        "Round 1 challenge",         // label for the challenge
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

    domsep = <DomainSeparator<DefaultHash> as FieldDomainSeparator<FpGoldilocks>>::add_scalars(
        domsep,
        1,
        "folded merkle root",
    );

    domsep = <DomainSeparator<DefaultHash> as FieldDomainSeparator<FpGoldilocks>>::challenge_scalars(
        domsep,
        1,               // number of scalars for the challenge
        "Index challenge",         // label for the challenge
    );

    let mut prover_state = domsep.to_prover_state();
  
    // Add transcript
    prover_state.add_scalars(&transcript).expect("Fiat shamir error!! Scalar addition failed");  
    
    // Generate challenge for composition
    let [alpha0,alpha1,alpha2,alpha3,alpha4]: [FpGoldilocks; 5] = prover_state.challenge_scalars().expect("Fiat shamir error!! Challenge genration failed");  

    //Composition polynomial
    let composition_poly = q_poly_0*alpha0 + q_poly_1*alpha1 + q_poly_second_final*alpha2 + q_poly_final*alpha3 + t_q_poly*alpha4;
    
    //Merkle commitment
    let RS_CODEWORDS:Vec<FpGoldilocks> = evaluate_poly_from_domain(&composition_poly,lde_evaluation_domain.clone()); // Evaluation of polynomial over the extended domain (Reed solomon codewords)
    let trace_merkle_root:FpGoldilocks = commit(RS_CODEWORDS.clone());

    //Sample for linear combination in folded polynomial
    prover_state.add_scalars(&[trace_merkle_root]).expect("Fiat shamir error!! Scalar addition failed"); 
    let [r_challenge]: [FpGoldilocks; 1] = prover_state.challenge_scalars().expect("Fiat shamir error!! Challenge genration failed");  
    
    // FRI
    let coeff_list:&[FpGoldilocks] = composition_poly.coeffs();
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
    let folded_domain:Vec<FpGoldilocks> = fold_domain(&lde_evaluation_domain);
    let folded_domain_len:usize = folded_domain.len();
    let folded_rs_codewords:Vec<FpGoldilocks> = evaluate_poly_from_domain(&folded_poly,folded_domain.clone()); // Evaluation of polynomial over the extended domain (Reed solomon codewords)
    let folded_root:FpGoldilocks =  commit(folded_rs_codewords.clone());

    //Verifier
    
    //Sample random index 'i' for query
    prover_state.add_scalars(&[folded_root]).expect("Fiat shamir error!! Scalar addition failed");  
    let [index_challenge]: [FpGoldilocks; 1] = prover_state.challenge_scalars().expect("Fiat shamir error!! Challenge genration failed");  
    let sample_index:usize = get_bounded_index(index_challenge,folded_domain_len);

    //Collinearity test
    // A = (w^i,f(w^i)), B = (-w^i,f(w^N/2+i)), C = (r, folded_f((w^i))^2)
    let x_list = vec![
        lde_evaluation_domain[sample_index],
        lde_evaluation_domain[(lde_evaluation_domain.len()/2) + sample_index],
    ];
    let y_list = vec![
        RS_CODEWORDS[sample_index],
        RS_CODEWORDS[(lde_evaluation_domain.len()/2) + sample_index],
    ];

    let a_b_poly:DensePolynomial<FpGoldilocks> = lagrange_interpolation(&x_list,y_list); //Intepolate A,B 
    let a_b_poly_eval = a_b_poly.evaluate(&r_challenge); //Colinearity test
    assert_eq!(a_b_poly_eval,folded_rs_codewords[sample_index]); // eval ===? f(w^i)^2

}

