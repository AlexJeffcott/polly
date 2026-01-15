use wasm_bindgen::prelude::*;
use chacha20poly1305::{
    aead::{Aead, KeyInit, OsRng},
    ChaCha20Poly1305, Nonce,
};
use rand::RngCore;

// Simplified crypto using ChaCha20-Poly1305
// In production, you'd want more robust key derivation and management

#[wasm_bindgen]
pub struct KeyPair {
    public_key: Vec<u8>,
    private_key: Vec<u8>,
}

#[wasm_bindgen]
impl KeyPair {
    /// Generate a new random keypair
    #[wasm_bindgen(constructor)]
    pub fn new() -> Result<KeyPair, JsValue> {
        let mut public_key = vec![0u8; 32];
        let mut private_key = vec![0u8; 32];

        OsRng.fill_bytes(&mut public_key);
        OsRng.fill_bytes(&mut private_key);

        Ok(KeyPair {
            public_key,
            private_key,
        })
    }

    /// Create keypair from existing keys
    #[wasm_bindgen]
    pub fn from_bytes(public_key: &[u8], private_key: &[u8]) -> Result<KeyPair, JsValue> {
        if public_key.len() != 32 || private_key.len() != 32 {
            return Err(JsValue::from_str("Keys must be 32 bytes"));
        }

        Ok(KeyPair {
            public_key: public_key.to_vec(),
            private_key: private_key.to_vec(),
        })
    }

    /// Get public key bytes
    #[wasm_bindgen(getter)]
    pub fn public_key(&self) -> Vec<u8> {
        self.public_key.clone()
    }

    /// Get private key bytes
    #[wasm_bindgen(getter)]
    pub fn private_key(&self) -> Vec<u8> {
        self.private_key.clone()
    }

    /// Export as hex string for easy storage
    #[wasm_bindgen]
    pub fn to_hex(&self) -> String {
        format!(
            "{}:{}",
            hex::encode(&self.public_key),
            hex::encode(&self.private_key)
        )
    }

    /// Import from hex string
    #[wasm_bindgen]
    pub fn from_hex(hex_str: &str) -> Result<KeyPair, JsValue> {
        let parts: Vec<&str> = hex_str.split(':').collect();
        if parts.len() != 2 {
            return Err(JsValue::from_str("Invalid hex format"));
        }

        let public_key = hex::decode(parts[0])
            .map_err(|e| JsValue::from_str(&format!("Invalid public key hex: {}", e)))?;
        let private_key = hex::decode(parts[1])
            .map_err(|e| JsValue::from_str(&format!("Invalid private key hex: {}", e)))?;

        KeyPair::from_bytes(&public_key, &private_key)
    }
}

/// Generate a random workspace key (32 bytes)
#[wasm_bindgen]
pub fn generate_workspace_key() -> Vec<u8> {
    let mut key = vec![0u8; 32];
    OsRng.fill_bytes(&mut key);
    key
}

/// Encrypt data with a symmetric key (ChaCha20-Poly1305)
#[wasm_bindgen]
pub fn encrypt(data: &[u8], key: &[u8]) -> Result<Vec<u8>, JsValue> {
    if key.len() != 32 {
        return Err(JsValue::from_str("Key must be 32 bytes"));
    }

    let cipher = ChaCha20Poly1305::new_from_slice(key)
        .map_err(|e| JsValue::from_str(&format!("Invalid key: {}", e)))?;

    // Generate random nonce
    let mut nonce_bytes = [0u8; 12];
    OsRng.fill_bytes(&mut nonce_bytes);
    let nonce = Nonce::from_slice(&nonce_bytes);

    // Encrypt
    let ciphertext = cipher
        .encrypt(nonce, data)
        .map_err(|e| JsValue::from_str(&format!("Encryption failed: {}", e)))?;

    // Prepend nonce to ciphertext
    let mut result = nonce_bytes.to_vec();
    result.extend(ciphertext);

    Ok(result)
}

/// Decrypt data with a symmetric key
#[wasm_bindgen]
pub fn decrypt(encrypted: &[u8], key: &[u8]) -> Result<Vec<u8>, JsValue> {
    if key.len() != 32 {
        return Err(JsValue::from_str("Key must be 32 bytes"));
    }

    if encrypted.len() < 12 {
        return Err(JsValue::from_str("Invalid ciphertext: too short"));
    }

    let cipher = ChaCha20Poly1305::new_from_slice(key)
        .map_err(|e| JsValue::from_str(&format!("Invalid key: {}", e)))?;

    // Extract nonce and ciphertext
    let nonce = Nonce::from_slice(&encrypted[..12]);
    let ciphertext = &encrypted[12..];

    // Decrypt
    let plaintext = cipher
        .decrypt(nonce, ciphertext)
        .map_err(|e| JsValue::from_str(&format!("Decryption failed: {}", e)))?;

    Ok(plaintext)
}

/// Encrypt text (convenience function)
#[wasm_bindgen]
pub fn encrypt_text(text: &str, key: &[u8]) -> Result<Vec<u8>, JsValue> {
    encrypt(text.as_bytes(), key)
}

/// Decrypt to text (convenience function)
#[wasm_bindgen]
pub fn decrypt_text(encrypted: &[u8], key: &[u8]) -> Result<String, JsValue> {
    let plaintext = decrypt(encrypted, key)?;
    String::from_utf8(plaintext)
        .map_err(|e| JsValue::from_str(&format!("Invalid UTF-8: {}", e)))
}

/// Convert bytes to base64 (for transmission)
#[wasm_bindgen]
pub fn to_base64(data: &[u8]) -> String {
    base64::encode(data)
}

/// Convert base64 to bytes
#[wasm_bindgen]
pub fn from_base64(s: &str) -> Result<Vec<u8>, JsValue> {
    base64::decode(s).map_err(|e| JsValue::from_str(&format!("Invalid base64: {}", e)))
}

// For hex encoding
mod hex {
    pub fn encode(bytes: &[u8]) -> String {
        bytes.iter().map(|b| format!("{:02x}", b)).collect()
    }

    pub fn decode(s: &str) -> Result<Vec<u8>, String> {
        if s.len() % 2 != 0 {
            return Err("Hex string must have even length".to_string());
        }

        (0..s.len())
            .step_by(2)
            .map(|i| {
                u8::from_str_radix(&s[i..i + 2], 16)
                    .map_err(|e| format!("Invalid hex: {}", e))
            })
            .collect()
    }
}

// For base64 encoding
mod base64 {
    const CHARS: &[u8] = b"ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789+/";

    pub fn encode(data: &[u8]) -> String {
        let mut result = String::new();
        let mut i = 0;

        while i < data.len() {
            let b1 = data[i];
            let b2 = if i + 1 < data.len() { data[i + 1] } else { 0 };
            let b3 = if i + 2 < data.len() { data[i + 2] } else { 0 };

            result.push(CHARS[(b1 >> 2) as usize] as char);
            result.push(CHARS[(((b1 & 0x03) << 4) | (b2 >> 4)) as usize] as char);
            result.push(if i + 1 < data.len() {
                CHARS[(((b2 & 0x0f) << 2) | (b3 >> 6)) as usize] as char
            } else {
                '='
            });
            result.push(if i + 2 < data.len() {
                CHARS[(b3 & 0x3f) as usize] as char
            } else {
                '='
            });

            i += 3;
        }

        result
    }

    pub fn decode(s: &str) -> Result<Vec<u8>, String> {
        let s = s.trim_end_matches('=');
        let mut result = Vec::new();
        let bytes: Vec<u8> = s.bytes().collect();
        let mut i = 0;

        while i < bytes.len() {
            let c1 = char_to_value(bytes[i])?;
            let c2 = if i + 1 < bytes.len() { char_to_value(bytes[i + 1])? } else { 0 };
            let c3 = if i + 2 < bytes.len() { char_to_value(bytes[i + 2])? } else { 0 };
            let c4 = if i + 3 < bytes.len() { char_to_value(bytes[i + 3])? } else { 0 };

            result.push((c1 << 2) | (c2 >> 4));
            if i + 2 < bytes.len() {
                result.push((c2 << 4) | (c3 >> 2));
            }
            if i + 3 < bytes.len() {
                result.push((c3 << 6) | c4);
            }

            i += 4;
        }

        Ok(result)
    }

    fn char_to_value(c: u8) -> Result<u8, String> {
        match c {
            b'A'..=b'Z' => Ok(c - b'A'),
            b'a'..=b'z' => Ok(c - b'a' + 26),
            b'0'..=b'9' => Ok(c - b'0' + 52),
            b'+' => Ok(62),
            b'/' => Ok(63),
            _ => Err(format!("Invalid base64 character: {}", c as char)),
        }
    }
}
