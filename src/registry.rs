use nft_smt::common::{Byte32, BytesBuilder};
use nft_smt::molecule::prelude::*;
use nft_smt::registry::{
    CompactNFTRegistryEntriesBuilder, KVPair, KVPairBuilder, KVPairVecBuilder,
};
use nft_smt::smt::{Blake2bHasher, H256, SMT};

fn generate_smt(origin_lock_hashes: Vec<[u8; 32]>, lock_hashes: Vec<[u8; 32]>) -> (String, String) {
    let mut smt = SMT::default();
    let update_leaves_count = lock_hashes.len();

    if !origin_lock_hashes.is_empty() {
        for lock_hash in origin_lock_hashes {
            let key: H256 = H256::from(lock_hash);
            let value: H256 = H256::from([255u8; 32]);
            smt.update(key, value).expect("SMT update leave error");
        }
    }

    let mut update_leaves: Vec<(H256, H256)> = Vec::with_capacity(update_leaves_count);
    for lock_hash in lock_hashes {
        let key: H256 = H256::from(lock_hash);
        let value: H256 = H256::from([255u8; 32]);
        update_leaves.push((key, value));
        smt.update(key, value).expect("SMT update leave error");
    }
    let root_hash = smt.root().clone();

    let mut root_hash_bytes = [0u8; 32];
    root_hash_bytes.copy_from_slice(root_hash.as_slice());
    let root_hash_hex = hex::encode(root_hash_bytes);

    println!("smt root hash: {:?}", root_hash_hex);

    let registry_merkle_proof = smt
        .merkle_proof(update_leaves.iter().map(|leave| leave.0).collect())
        .unwrap();
    let registry_merkle_proof_compiled = registry_merkle_proof
        .compile(update_leaves.clone())
        .unwrap();
    let verify_result = registry_merkle_proof_compiled
        .verify::<Blake2bHasher>(&root_hash, update_leaves.clone())
        .expect("smt proof verify failed");
    assert!(verify_result, "smt proof verify failed");

    let merkel_proof_vec: Vec<u8> = registry_merkle_proof_compiled.into();

    println!("smt proof: {:?}", merkel_proof_vec);

    let kv_pair_vec = update_leaves
        .iter()
        .map(|leave| {
            let key: [u8; 32] = leave.0.into();
            let value: [u8; 32] = leave.1.into();
            KVPairBuilder::default()
                .k(Byte32::from_slice(&key).unwrap())
                .v(Byte32::from_slice(&value).unwrap())
                .build()
        })
        .collect::<Vec<KVPair>>();

    let entries_builder = CompactNFTRegistryEntriesBuilder::default();
    let kv_pair_vec_builder = KVPairVecBuilder::default();
    let merkel_proof_bytes = BytesBuilder::default()
        .extend(merkel_proof_vec.iter().map(|v| Byte::from(*v)))
        .build();

    let witness_data = entries_builder
        .kv_state(kv_pair_vec_builder.set(kv_pair_vec).build())
        .kv_proof(merkel_proof_bytes)
        .build();

    let witness_data_hex = hex::encode(witness_data.as_slice());

    println!("witness_data_hex: {:?}", witness_data_hex);

    (root_hash_hex, witness_data_hex)
}

#[test]
fn create_smt() {
    let lock_hash: [u8; 32] = [
        234, 40, 201, 143, 56, 180, 165, 122, 168, 23, 86, 177, 103, 187, 55, 250, 66, 218, 246,
        126, 219, 201, 134, 58, 251, 129, 114, 9, 110, 211, 1, 194,
    ];
    println!("{:?}", hex::encode(&lock_hash));
    let lock_hashes = vec![lock_hash];
    let (root_hash, witness_data) = generate_smt(vec![], lock_hashes);
    assert_eq!(
        root_hash,
        "b6719be3614c76a651b86562c1f35f7cc8d4d2a129dfc75759fc82d601ae5670"
    );
    assert_eq!(witness_data, "570000000c0000005000000001000000ea28c98f38b4a57aa81756b167bb37fa42daf67edbc9863afb8172096ed301c2ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff030000004c4f00");
}

#[test]
fn update_smt() {
    let origin_lock_hash: [u8; 32] = [
        234, 40, 201, 143, 56, 180, 165, 122, 168, 23, 86, 177, 103, 187, 55, 250, 66, 218, 246,
        126, 219, 201, 134, 58, 251, 129, 114, 9, 110, 211, 1, 194,
    ];
    let origin_lock_hashes = vec![origin_lock_hash];

    let lock_hash: [u8; 32] = [
        50, 247, 246, 45, 198, 8, 45, 245, 35, 87, 121, 193, 186, 170, 5, 86, 60, 208, 149, 227,
        148, 193, 36, 253, 2, 16, 17, 42, 160, 219, 182, 130,
    ];
    let lock_hashes = vec![lock_hash];

    let (root_hash, witness_data) = generate_smt(origin_lock_hashes, lock_hashes);
    assert_eq!(
        root_hash,
        "bae562505da06ad2226ffc876b09d97b908e63820bb49a7f31d88833b34a800a"
    );
    assert_eq!(witness_data, "9b0000000c000000500000000100000032f7f62dc6082df5235779c1baaa05563cd095e394c124fd0210112aa0dbb682ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff470000004c4ffe51fe2eb9ab9a5e3041755a0ec60170a09b5187ee3b40a17e1cc7232e68b37302f014ea28c98f38b4a57aa81756b167bb37fa42daf67edbc9863afb8172096ed301024f01");
}
