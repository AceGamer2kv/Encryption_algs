import hashlib
import sys

# ==========================================
# 1. SIMPLE DATA ENCRYPTION STANDARD (S-DES)
# ==========================================
class SDES:
    P10 = [3, 5, 2, 7, 4, 10, 1, 9, 8, 6]
    P8  = [6, 3, 7, 4, 8, 5, 10, 9]
    IP  = [2, 6, 3, 1, 4, 8, 5, 7]
    IPI = [4, 1, 3, 5, 7, 2, 8, 6]
    EP  = [4, 1, 2, 3, 2, 3, 4, 1]
    P4  = [2, 4, 3, 1]
    
    S0 = [[1, 0, 3, 2], [3, 2, 1, 0], [0, 2, 1, 3], [3, 1, 3, 2]]
    S1 = [[0, 1, 2, 3], [2, 0, 1, 3], [3, 0, 1, 0], [2, 1, 0, 3]]

    @staticmethod
    def permute(bits, table):
        return "".join(bits[i - 1] for i in table)

    @staticmethod
    def left_shift(bits, n):
        return bits[n:] + bits[:n]

    def generate_keys(self, key10):
        p10 = self.permute(key10, self.P10)
        left, right = p10[:5], p10[5:]
        
        left1, right1 = self.left_shift(left, 1), self.left_shift(right, 1)
        k1 = self.permute(left1 + right1, self.P8)
        
        left2, right2 = self.left_shift(left1, 2), self.left_shift(right1, 2)
        k2 = self.permute(left2 + right2, self.P8)
        
        return k1, k2

    def fk(self, bits, subkey):
        left, right = bits[:4], bits[4:]
        ep = self.permute(right, self.EP)
        xored = f"{int(ep, 2) ^ int(subkey, 2):08b}"
        
        r0, c0 = int(xored[0] + xored[3], 2), int(xored[1] + xored[2], 2)
        s0_out = f"{self.S0[r0][c0]:02b}"
        
        r1, c1 = int(xored[4] + xored[7], 2), int(xored[5] + xored[6], 2)
        s1_out = f"{self.S1[r1][c1]:02b}"
        
        p4 = self.permute(s0_out + s1_out, self.P4)
        return f"{int(left, 2) ^ int(p4, 2):04b}" + right

    def transform(self, block8, k1, k2):
        ip = self.permute(block8, self.IP)
        f1 = self.fk(ip, k1)
        swapped = f1[4:] + f1[:4]
        f2 = self.fk(swapped, k2)
        return self.permute(f2, self.IPI)

    def encrypt(self, block8, key10):
        k1, k2 = self.generate_keys(key10)
        return self.transform(block8, k1, k2)

    def decrypt(self, block8, key10):
        k1, k2 = self.generate_keys(key10)
        return self.transform(block8, k2, k1)


# ==========================================
# 2. RSA (STRING CIPHERTEXT DISPLAY)
# ==========================================
class RSA:
    @staticmethod
    def gcd(a, b):
        while b:
            a, b = b, a % b
        return a

    @staticmethod
    def mod_inverse(e, phi):
        def extended_gcd(a, b):
            if a == 0:
                return b, 0, 1
            gcd, x1, y1 = extended_gcd(b % a, a)
            return gcd, y1 - (b // a) * x1, x1
        
        _, x, _ = extended_gcd(e, phi)
        return (x % phi + phi) % phi

    def generate_keypair(self, p=61, q=53):
        n = p * q
        phi = (p - 1) * (q - 1)
        e = 17
        while self.gcd(e, phi) != 1:
            e += 2
        d = self.mod_inverse(e, phi)
        return (e, n), (d, n)

    def encrypt_to_integers(self, text, public_key):
        e, n = public_key
        return [pow(ord(char), e, n) for char in text]

    def decrypt_from_integers(self, ciphertext_list, private_key):
        d, n = private_key
        decrypted_chars = [chr(pow(code, d, n)) for code in ciphertext_list]
        return "".join(decrypted_chars)

    @staticmethod
    def integers_to_string(cipher_integers):
        """Maps raw RSA integer values to printable Unicode string characters."""
        return "".join(chr((code % 94) + 33) for code in cipher_integers)


# ==========================================
# 3. ELLIPTIC CURVE CRYPTOGRAPHY (ECC)
# ==========================================
class ECC:
    def __init__(self, a=2, b=3, p=97):
        self.a = a
        self.b = b
        self.p = p

    def is_on_curve(self, P):
        if P is None:
            return True
        x, y = P
        return (y**2) % self.p == (x**3 + self.a * x + self.b) % self.p

    def add_points(self, P, Q):
        if P is None: return Q
        if Q is None: return P
        
        x1, y1 = P
        x2, y2 = Q

        if x1 == x2 and (y1 != y2 or y1 == 0):
            return None
        
        if P != Q:
            m = ((y2 - y1) * pow(x2 - x1, -1, self.p)) % self.p
        else:
            m = ((3 * x1**2 + self.a) * pow(2 * y1, -1, self.p)) % self.p

        x3 = (m**2 - x1 - x2) % self.p
        y3 = (m * (x1 - x3) - y1) % self.p
        return (x3, y3)

    def scalar_mult(self, k, P):
        result = None
        current = P
        while k > 0:
            if k % 2 == 1:
                result = self.add_points(result, current)
            current = self.add_points(current, current)
            k //= 2
        return result

    def encrypt(self, M_point, public_key, G, k=5):
        C1 = self.scalar_mult(k, G)
        shared_secret = self.scalar_mult(k, public_key)
        C2 = self.add_points(M_point, shared_secret)
        return C1, C2

    def decrypt(self, ciphertext, private_key):
        C1, C2 = ciphertext
        shared_secret = self.scalar_mult(private_key, C1)
        neg_secret = (shared_secret[0], (-shared_secret[1]) % self.p)
        return self.add_points(C2, neg_secret)


# ==========================================
# 4. HASHING (SHA-256)
# ==========================================
class Hashing:
    @staticmethod
    def hash_sha256(data_str):
        return hashlib.sha256(data_str.encode('utf-8')).hexdigest()


# ==========================================
# INTERACTIVE CLI APPLICATION
# ==========================================
def safe_input(prompt):
    """Handles Ctrl+C and Ctrl+D gracefully during input prompts."""
    try:
        return input(prompt)
    except (KeyboardInterrupt, EOFError):
        print("\n\nUser requested exit. Goodbye!")
        sys.exit(0)

def main():
    sdes = SDES()
    rsa = RSA()
    ecc = ECC(a=2, b=3, p=97)
    
    while True:
        print("\n==========================================")
        print(" CRYPTOGRAPHIC ALGORITHMS DEMONSTRATOR")
        print("==========================================")
        print("1. S-DES (Symmetric Encryption)")
        print("2. RSA (Asymmetric Encryption - String Output)")
        print("3. ECC (Elliptic Curve Cryptography)")
        print("4. Cryptographic Hashing (SHA-256)")
        print("5. Exit")
        
        choice = safe_input("\nSelect an algorithm (1-5): ").strip()

        if choice == '1':
            print("\n--- 1. Simple DES (S-DES) ---")
            try:
                plaintext = safe_input("Enter 8-bit binary plaintext (e.g., 10101011): ").strip()
                if len(plaintext) != 8 or not set(plaintext).issubset({'0', '1'}):
                    raise ValueError("Plaintext must be exactly 8 binary digits (0s and 1s).")

                key = safe_input("Enter 10-bit binary key (e.g., 1010000010): ").strip()
                if len(key) != 10 or not set(key).issubset({'0', '1'}):
                    raise ValueError("Key must be exactly 10 binary digits (0s and 1s).")

                ciphertext = sdes.encrypt(plaintext, key)
                decrypted = sdes.decrypt(ciphertext, key)
                
                print(f"\n-> Forward Process (Encryption):  {plaintext}  ==> Ciphertext: {ciphertext}")
                print(f"<- Backward Process (Decryption): {ciphertext} ==> Plaintext:  {decrypted}")
                print(f"Reversible: {plaintext == decrypted}")

            except ValueError as ve:
                print(f"\n[Input Error]: {ve}")
            except Exception as e:
                print(f"\n[Unexpected Error]: {e}")

        elif choice == '2':
            print("\n--- 2. RSA String Encryption ---")
            try:
                pub_key, priv_key = rsa.generate_keypair(p=61, q=53)
                print(f"Generated Public Key  (e, n): {pub_key}")
                print(f"Generated Private Key (d, n): {priv_key}\n")
                
                text_input = safe_input("Enter a string message: ")
                if not text_input:
                    raise ValueError("String message cannot be empty.")

                ascii_values = [ord(c) for c in text_input]
                if any(code >= pub_key[1] for code in ascii_values):
                    raise ValueError("Input string contains characters with ASCII value exceeding modulus n.")

                cipher_integers = rsa.encrypt_to_integers(text_input, pub_key)
                ciphertext_string = rsa.integers_to_string(cipher_integers)
                decrypted_text = rsa.decrypt_from_integers(cipher_integers, priv_key)
                
                print(f"\n-> Forward Process (Encryption):")
                print(f"   Original Plaintext : '{text_input}'")
                print(f"   Ciphertext String  : '{ciphertext_string}'")
                
                print(f"\n<- Backward Process (Decryption):")
                print(f"   Reconstructed Text : '{decrypted_text}'")
                print(f"Reversible: {text_input == decrypted_text}")

            except ValueError as ve:
                print(f"\n[Input Error]: {ve}")
            except Exception as e:
                print(f"\n[Unexpected Error]: {e}")

        elif choice == '3':
            print("\n--- 3. Elliptic Curve Cryptography (ECC) ---")
            try:
                print("Curve Equation: y^2 = x^3 + 2x + 3 (mod 97)")
                G = (3, 6)
                priv_key = 7
                pub_key = ecc.scalar_mult(priv_key, G)
                
                print(f"Base Point (G): {G}")
                print(f"Private Key (d): {priv_key}")
                print(f"Public Key (Q = d*G): {pub_key}")
                
                use_custom = safe_input("\nUse default plaintext point (10, 32)? [Y/n]: ").strip().lower()
                
                if use_custom == 'n':
                    x_str = safe_input("Enter integer X coordinate: ").strip()
                    y_str = safe_input("Enter integer Y coordinate: ").strip()
                    
                    if not x_str.isdigit() or not y_str.isdigit():
                        raise ValueError("Coordinates must be non-negative integers.")
                    
                    M = (int(x_str) % ecc.p, int(y_str) % ecc.p)
                    
                    if not ecc.is_on_curve(M):
                        raise ValueError(f"Point {M} does not satisfy the curve equation y^2 = x^3 + 2x + 3 (mod 97).")
                else:
                    M = (10, 32)

                print(f"\nPlaintext Point (M): {M}")
                
                ciphertext = ecc.encrypt(M, pub_key, G, k=5)
                decrypted_point = ecc.decrypt(ciphertext, priv_key)
                
                print(f"\n-> Forward Process (Encryption):  Point {M} ==> Ciphertext (C1, C2): {ciphertext}")
                print(f"<- Backward Process (Decryption): Ciphertext {ciphertext} ==> Point: {decrypted_point}")
                print(f"Reversible: {M == decrypted_point}")

            except ValueError as ve:
                print(f"\n[Input Error]: {ve}")
            except Exception as e:
                print(f"\n[Unexpected Error]: {e}")

        elif choice == '4':
            print("\n--- 4. Hashing (SHA-256) ---")
            try:
                text = safe_input("Enter any string message to hash: ")
                if not text:
                    print("Note: Computing SHA-256 hash for an empty string.")

                hash_val = Hashing.hash_sha256(text)
                
                print(f"\n-> Forward Process (Hash Computation): '{text}' ==> SHA-256: {hash_val}")
                print("<- Backward Process (Reverse Calculation): [BLOCKED]")
                print("Explanation: SHA-256 is a one-way function protected by pre-image resistance. "
                      "It is mathematically infeasible to recover original data from a hash value.")
                print("Reversible: No")

            except Exception as e:
                print(f"\n[Unexpected Error]: {e}")

        elif choice == '5':
            print("\nExiting application. Goodbye!")
            break
        else:
            print("\n[Input Error]: Invalid choice. Please enter a number between 1 and 5.")

if __name__ == "__main__":
    main()