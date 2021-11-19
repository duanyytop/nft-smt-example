use nft_smt::common::{Byte32, Byte32Builder, BytesBuilder, CompactNFTId, CompactNFTInfo, OutPointBytesBuilder};
use nft_smt::mint::{MintCompactNFTEntries, MintCompactNFTValue};
use nft_smt::smt::{blake2b_256, Blake2bHasher, H256, SMT};
use nft_smt::transfer::{ClaimedCommpactNFTValueVecBuilder, ClaimedCompactNFTKey, ClaimedCompactNFTKeyBuilder, ClaimedCompactNFTKeyVecBuilder, ClaimMintCompactNFTEntriesBuilder, CompactNFTKey, CompactNFTKeyBuilder, CompactNFTKeyVecBuilder, OwnedCompactNFTValueVecBuilder};

use nft_smt::molecule::prelude::*;
use nft_smt::ckb_types::packed::{OutPointBuilder, OutPoint};

pub const BYTE3_ZEROS: [u8; 3] = [0u8; 3];
pub const BYTE22_ZEROS: [u8; 22] = [0u8; 22];

fn generate_claimed_compact_nft_from_mint(
    input_compact_nft_out_point: OutPoint,
    mint_nft_keys: Vec<CompactNFTId>,
    mint_nft_values: Vec<MintCompactNFTValue>,
    class_mint_proof: Vec<u8>,
    claim_leaves_count: usize,
) -> (H256, Vec<u8>) {
    let mut smt = SMT::default();
    let mut owned_nft_keys: Vec<CompactNFTKey> = Vec::new();
    let mut owned_nft_values: Vec<CompactNFTInfo> = Vec::new();
    let mut claimed_nft_keys: Vec<ClaimedCompactNFTKey> = Vec::new();
    let mut claimed_nft_values: Vec<Byte32> = Vec::new();
    let mut update_leaves: Vec<(H256, H256)> = Vec::with_capacity(claim_leaves_count * 2);
    for index in 0..claim_leaves_count {
        // Generate owned_nft smt kv pairs
        let mint_nft_key = mint_nft_keys.get(index).unwrap().clone();
        let mut nft_id_vec = Vec::new();
        nft_id_vec.extend(&BYTE3_ZEROS);
        nft_id_vec.extend(&[1u8]);
        nft_id_vec.extend(&mint_nft_key.as_slice().to_vec());
        let mut nft_id_bytes = [0u8; 32];
        nft_id_bytes.copy_from_slice(&nft_id_vec);
        let mut key = H256::from(nft_id_bytes);

        println!("mint_nft_key: {:?}", mint_nft_key);

        let owned_nft_key = CompactNFTKeyBuilder::default()
            .smt_type(Byte::from(1u8))
            .nft_id(mint_nft_key.clone())
            .build();
        owned_nft_keys.push(owned_nft_key);

        let mint_nft_value = mint_nft_values.get(index).unwrap().clone();
        let mut owed_nft_value_vec = Vec::new();
        owed_nft_value_vec.extend(&BYTE22_ZEROS);
        owed_nft_value_vec.extend(mint_nft_value.nft_info().as_slice());
        let mut owned_nft_value = [0u8; 32];
        owned_nft_value.copy_from_slice(&owed_nft_value_vec);

        owned_nft_values.push(mint_nft_value.nft_info().clone());
        let mut value: H256 = H256::from(owned_nft_value);

        update_leaves.push((key, value));
        smt.update(key, value).expect("SMT update leave error");

        // Generate claimed_nft smt kv pairs
        let compact_out_point_vec = input_compact_nft_out_point
            .as_bytes()
            .slice(12..36)
            .to_vec()
            .iter()
            .map(|v| Byte::from(*v))
            .collect::<Vec<Byte>>();
        let mut compact_out_point_bytes: [Byte; 24] = [Byte::from(0u8); 24];
        compact_out_point_bytes.copy_from_slice(&compact_out_point_vec);
        let compact_out_point = OutPointBytesBuilder::default()
            .set(compact_out_point_bytes)
            .build();
        let nft_key_ = CompactNFTKeyBuilder::default()
            .nft_id(mint_nft_key.clone())
            .smt_type(Byte::from(2u8))
            .build();
        let claimed_nft_key = ClaimedCompactNFTKeyBuilder::default()
            .nft_key(nft_key_)
            .out_point(compact_out_point)
            .build();
        claimed_nft_keys.push(claimed_nft_key.clone());
        key = H256::from(blake2b_256(claimed_nft_key.as_slice()));

        value = H256::from([255u8; 32]);
        claimed_nft_values.push(
            Byte32Builder::default()
                .set([Byte::from(255u8); 32])
                .build(),
        );

        update_leaves.push((key, value));
        smt.update(key, value).expect("SMT update leave error");
    }
    let root_hash = smt.root().clone();

    let claim_mint_merkle_proof = smt
        .merkle_proof(update_leaves.iter().map(|leave| leave.0).collect())
        .unwrap();
    let claim_mint_merkle_proof_compiled = claim_mint_merkle_proof
        .compile(update_leaves.clone())
        .unwrap();
    let verify_result = claim_mint_merkle_proof_compiled
        .verify::<Blake2bHasher>(&root_hash, update_leaves.clone())
        .expect("smt proof verify failed");

    assert!(verify_result, "smt proof verify failed");

    let merkel_proof_vec: Vec<u8> = claim_mint_merkle_proof_compiled.into();

    let merkel_proof_bytes = BytesBuilder::default()
        .extend(merkel_proof_vec.iter().map(|v| Byte::from(*v)))
        .build();

    let mint_merkel_proof_bytes = BytesBuilder::default()
        .extend(class_mint_proof.iter().map(|v| Byte::from(*v)))
        .build();

    let mint_entries = ClaimMintCompactNFTEntriesBuilder::default()
        .owned_nft_keys(
            CompactNFTKeyVecBuilder::default()
                .set(owned_nft_keys)
                .build(),
        )
        .owned_nft_values(
            OwnedCompactNFTValueVecBuilder::default()
                .set(owned_nft_values)
                .build(),
        )
        .claimed_nft_keys(
            ClaimedCompactNFTKeyVecBuilder::default()
                .set(claimed_nft_keys)
                .build(),
        )
        .claimed_nft_values(
            ClaimedCommpactNFTValueVecBuilder::default()
                .set(claimed_nft_values)
                .build(),
        )
        .proof(merkel_proof_bytes)
        .mint_proof(mint_merkel_proof_bytes)
        .build();

    (
        root_hash,
        Vec::from(mint_entries.as_slice()),
    )
}

#[test]
fn test_claim_from_mint() {
    let mut tx_hash_bytes: [u8; 32] = [0u8; 32];
    tx_hash_bytes.copy_from_slice(&hex::decode("b30aec8032f7ad2aa55cf198238bd41c4a735c4767640fa50b45fc9a951f892b").unwrap());
    // Uint32 little endian
    let index = [1u8, 0u8, 0u8, 0u8].map(|v| nft_smt::ckb_types::packed::Byte::from(v));
    let input_compact_nft_out_point = OutPointBuilder::default()
        .tx_hash(nft_smt::ckb_types::packed::Byte32::new(tx_hash_bytes))
        .index(nft_smt::ckb_types::packed::Uint32Builder::default().set(index).build())
        .build();
    println!("input_compact_nft_out_point: {:?}", input_compact_nft_out_point);

    let mint_entries_bytes = hex::decode("c500000010000000300000009b000000010000003939ecec56db8161b6308c84d6f5f9f12d00d1f000000003000000026b00000008000000630000000c000000160000000505050505050505000049000000490000001000000030000000310000009bd7e06f3ecf4be0f2fcd2188b23f1b9fcc88e5d4b65a8637b17723bbda3cce80114000000e616d1460d634668b8ad81971c3a53e705f51e60260000004c4ff950f6e4f07b5fd967f402d09cdb20e02d3acba1016f7c31666e51fa4005b8c9fb924f06").unwrap();
    let mint_entries = MintCompactNFTEntries::from_slice(&mint_entries_bytes).unwrap();

    let mut mint_nft_keys = Vec::new();
    for nft_key in mint_entries.nft_keys().into_iter() {
        mint_nft_keys.push(nft_key);
    }
    let mut mint_nft_values = Vec::new();
    for nft_value in mint_entries.nft_values().into_iter() {
        mint_nft_values.push(nft_value);
    }

    let class_mint_proof = mint_entries.proof().raw_data().to_vec();

    let (root_hash, witness_data) = generate_claimed_compact_nft_from_mint(input_compact_nft_out_point, mint_nft_keys, mint_nft_values, class_mint_proof, 1);

    println!("root_hash: {:?}", hex::encode(root_hash.as_slice()));
    println!("witness_data: {:?}", hex::encode(witness_data));
}