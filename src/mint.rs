use nft_smt::common::{BytesBuilder, CharacteristicBuilder, CompactNFTId, CompactNFTIdBuilder, CompactNFTInfoBuilder, IssuerIdBuilder, Uint32Builder};
use nft_smt::mint::{MintCompactNFTEntriesBuilder, MintCompactNFTKeyVecBuilder, MintCompactNFTValue, MintCompactNFTValueBuilder, MintCompactNFTValueVecBuilder};
use nft_smt::smt::{blake2b_256, Blake2bHasher, H256, SMT};
use nft_smt::molecule::prelude::*;
use nft_smt::ckb_types::packed::*;

pub const BYTE4_ZEROS: [u8; 4] = [0u8; 4];

fn generate_mint_smt(
    class_type_args: Vec<u8>,
    origin_receiver_lock_scripts: Vec<Script>,
    receiver_lock_scripts: Vec<Script>,
) -> (H256, Vec<u8>) {
    let class_type_args_bytes =
        class_type_args
            .iter()
            .map(|v| Byte::from(*v))
            .collect::<Vec<Byte>>();

    let origin_leaves_count = origin_receiver_lock_scripts.len();
    let update_leaves_count = receiver_lock_scripts.len();
    let mut smt = SMT::default();

    let mut nft_keys: Vec<CompactNFTId> = Vec::new();
    let mut nft_values: Vec<MintCompactNFTValue> = Vec::new();
    let mut update_leaves: Vec<(H256, H256)> = Vec::with_capacity(update_leaves_count);
    let mut receiver_lock_script_list = origin_receiver_lock_scripts;
    receiver_lock_script_list.extend(receiver_lock_scripts);
    for (index, lock_script) in receiver_lock_script_list.iter().enumerate() {
        let mut issuer_id_bytes = [Byte::from(0); 20];
        issuer_id_bytes.copy_from_slice(&class_type_args_bytes[0..20]);
        let issuer_id = IssuerIdBuilder::default().set(issuer_id_bytes).build();

        let mut class_id_bytes = [Byte::from(0); 4];
        class_id_bytes.copy_from_slice(&class_type_args_bytes[20..24]);
        let class_id = Uint32Builder::default().set(class_id_bytes).build();

        let token_id_vec = (index as u32)
            .to_be_bytes()
            .iter()
            .map(|v| Byte::from(*v))
            .collect::<Vec<Byte>>();
        let mut token_id_bytes = [Byte::from(0); 4];
        token_id_bytes.copy_from_slice(&token_id_vec);
        let token_id = Uint32Builder::default().set(token_id_bytes).build();
        let nft_id = CompactNFTIdBuilder::default()
            .issuer_id(issuer_id)
            .class_id(class_id)
            .token_id(token_id)
            .build();

        println!("nft_id: {:?}", nft_id.as_slice());

        if index >= origin_leaves_count {
            nft_keys.push(nft_id.clone());
        }

        let mut nft_id_vec = Vec::new();
        nft_id_vec.extend(&BYTE4_ZEROS);
        nft_id_vec.extend(&nft_id.as_slice().to_vec());
        let mut nft_id_bytes = [0u8; 32];
        nft_id_bytes.copy_from_slice(&nft_id_vec);
        let key = H256::from(nft_id_bytes);

        let characteristic = CharacteristicBuilder::default()
            .set([Byte::from(5); 8])
            .build();
        let receiver_lock = lock_script
            .as_slice()
            .iter()
            .map(|v| Byte::from(*v))
            .collect();
        let nft_info = CompactNFTInfoBuilder::default()
            .characteristic(characteristic)
            .configure(Byte::from(0u8))
            .state(Byte::from(0u8))
            .build();
        let nft_value = MintCompactNFTValueBuilder::default()
            .nft_info(nft_info.clone())
            .receiver_lock(BytesBuilder::default().set(receiver_lock).build())
            .build();

        if index >= origin_leaves_count {
            nft_values.push(nft_value.clone());
        }

        let value: H256 = H256::from(blake2b_256(nft_value.as_slice()));
        smt.update(key, value).expect("SMT update leave error");

        if index >= origin_leaves_count {
            update_leaves.push((key, value));
        }
    }
    let root_hash = smt.root().clone();

    let mint_merkle_proof = smt
        .merkle_proof(update_leaves.iter().map(|leave| leave.0).collect())
        .unwrap();
    let mint_merkle_proof_compiled = mint_merkle_proof.compile(update_leaves.clone()).unwrap();
    let verify_result = mint_merkle_proof_compiled
        .verify::<Blake2bHasher>(&root_hash, update_leaves.clone())
        .expect("smt proof verify failed");
    assert!(verify_result, "smt proof verify failed");

    let merkel_proof_vec: Vec<u8> = mint_merkle_proof_compiled.into();

    let merkel_proof_bytes = BytesBuilder::default()
        .extend(merkel_proof_vec.iter().map(|v| Byte::from(*v)))
        .build();

    let mint_entries = MintCompactNFTEntriesBuilder::default()
        .nft_keys(MintCompactNFTKeyVecBuilder::default().set(nft_keys).build())
        .nft_values(
            MintCompactNFTValueVecBuilder::default()
                .set(nft_values)
                .build(),
        )
        .proof(merkel_proof_bytes)
        .build();

    (
        root_hash,
        Vec::from(mint_entries.as_slice()),
    )
}

#[test]
fn test_mint() {
    let class_args = hex::decode("3939ecec56db8161b6308c84d6f5f9f12d00d1f000000003").unwrap();

    let code_hash_vec: Vec<Byte> = hex::decode("9bd7e06f3ecf4be0f2fcd2188b23f1b9fcc88e5d4b65a8637b17723bbda3cce8").unwrap().iter().map(|v| Byte::from(*v)).collect();
    let mut code_hash_bytes = [Byte::from(0); 32];
    code_hash_bytes.copy_from_slice(&code_hash_vec);
    let code_hash = Byte32Builder::default().set(code_hash_bytes).build();
    let script = ScriptBuilder::default().code_hash(code_hash).hash_type(Byte::from(1u8)).build();

    let args1 = nft_smt::ckb_types::packed::BytesBuilder::default().extend(hex::decode("0861e2b008ec0f2b1e6856fb8a24198222e02f19").unwrap().iter().map(|v| Byte::from(*v))).build();
    let args2 = nft_smt::ckb_types::packed::BytesBuilder::default().extend(hex::decode("dc70f33de86fdf381b4fc5bf092bb23d02774801").unwrap().iter().map(|v| Byte::from(*v))).build();
    let args3 = nft_smt::ckb_types::packed::BytesBuilder::default().extend(hex::decode("e616d1460d634668b8ad81971c3a53e705f51e60").unwrap().iter().map(|v| Byte::from(*v))).build();

    let origin_receiver_lock_scripts: Vec<Script> = vec![args1, args2].into_iter().map(|args| script.clone().as_builder().args(args).build()).collect();
    let receiver_lock_scripts: Vec<Script> = vec![args3].into_iter().map(|args| script.clone().as_builder().args(args).build()).collect();
    let (root_hash, mint_entries) = generate_mint_smt(class_args, origin_receiver_lock_scripts, receiver_lock_scripts);

    println!("root_hash: {:?}", hex::encode(root_hash.as_slice()));
    println!("mint_entries: {:?}", hex::encode(mint_entries));
}