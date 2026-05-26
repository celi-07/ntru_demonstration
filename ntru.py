# NOTE:
# POLYNOMIAL REPRESENTATION: a + bx + ... + yx^(n-1) + zx*n = [ a, b, ..., y, z ] where the index corresponds to the power of x
# HIGHEST DEGREE OF POLYNOMIAL: list[-1] (last element of the list)


# Library Imports
import math


# TRIM FUNCTION
def trim(f):
    # Store the polynomial coefficients as a list
    f_list = list(f)
    
    # Iterate over the list in reverse and remove trailing zeros
    while len(f_list) > 0 and f_list[-1] == 0:
        f_list.pop()
    
    # If the list is empty after trimming, return an empty list
    if not f_list:
        return []
    
    # Return the trimmed list of coefficients
    return f_list


# POLYNOMIAL ADDITION FUNCTION
def poly_add(a, b, p=None):
    # Initialize the result list with zeros
    # NOTE: Length equal to the maximum of coefficient amounts
    res = [0] * max(len(a), len(b))
    
    # Iterate over the coefficients of the first polynomial and add them to the result
    for i in range(len(a)):
        res[i] += a[i]
    
    # Iterate over the coefficients of the second polynomial and add them to the result
    for i in range(len(b)):
        res[i] += b[i]
    
    # If a modulus p is provided, reduce the coefficients modulo p
    if p is not None:
        res = [c % p for c in res]
    
    # Return the trimmed result to remove any trailing zeros
    return trim(res)


# POLYNOMIAL SUBTRACTION FUNCTION
def poly_sub(a, b, p=None):
    # Initialize the result list with zeros
    # NOTE: Length equal to the maximum of coefficient amounts
    res = [0] * max(len(a), len(b))
    
    # Iterate over the coefficients of the first polynomial and add them to the result
    for i in range(len(a)):
        res[i] += a[i]
    
    # Iterate over the coefficients of the second polynomial and subtract them from the result
    for i in range(len(b)):
        res[i] -= b[i]
    
    # If a modulus p is provided, reduce the coefficients modulo p
    if p is not None:
        res = [c % p for c in res]
    
    # Return the trimmed result to remove any trailing zeros
    return trim(res)


# POLYNOMIAL MULTIPLICATION FUNCTION
def poly_mul(a, b, p=None):
    # If either polynomial is empty, the result is an empty polynomial 
    if a == [] or b == []:
        return []
    
    # Initialize the result list with zeros, with length equal to the sum of the lengths of the two input polynomials minus one
    res = [0] * (len(a) + len(b) - 1)
    
    # Iterate over the coefficients of the first polynomial
    for i in range(len(a)):
        # Iterate over the coefficients of the second polynomial
        for j in range(len(b)):
            # Multiply the coefficients and add to the coefficient's index
            res[i + j] += a[i] * b[j]
    
    # If a modulus p is provided, reduce the coefficients modulo p
    if p is not None:
        res = [c % p for c in res]
    
    # Return the trimmed result to remove any trailing zeros
    return trim(res)


# POLYNOMIAL DIVISION WITH REMAINDER FUNCTION
def poly_div_mod_prime(a, b, p):
    # Trim the input polynomials to remove trailing zeros
    a_list = trim(a)
    b_list = trim(b)
    
    # Check if there is an indication of a division by zero error
    if not b_list or b_list == []:
        raise ZeroDivisionError("Polynomial division by zero.")
    
    # Initialize the quotient list with zeros
    # NOTE: Length of quotient will be at most degree of difference + 1
    quot = [0] * max(1, len(a_list) - len(b_list) + 1)
    
    # Initialize the remainder list
    # NOTE: Start with the dividend polynomial
    rem = list(a_list)
    
    # Calculate the multiplicative inverse of the leading coefficient of the divisor
    # NOTE: Uses Fermat's Little Theorem to compute the inverse
    lead_b_inv = pow(b_list[-1], p - 2, p)
    
    # Perform the polynomial long division process
    while len(rem) >= len(b_list) and rem!= []:
        # Calculate the degree difference
        deg_diff = len(rem) - len(b_list)
        
        # Calculate the factor to be subtracted from the remainder
        factor = (rem[-1] * lead_b_inv) % p
        
        # Place the calculated factor in the degree difference coefficient's index
        quot[deg_diff] = factor
        
        # Iterate over the coefficients of the divisor polynomial
        for i in range(len(b_list)):
            # Calculate the index of the remainder polynomial
            idx = i + deg_diff
            
            # Update the coefficient of the remainder polynomial
            rem[idx] = (rem[idx] - factor * b_list[i]) % p
        
        # Trim the remainder after each substraction
        rem = trim(rem)
    
    # Return the trimmed quotient and remainder polynomials
    return trim(quot), trim(rem)


# EXTENDED EUCLIDEAN ALGORITHM FOR POLYNOMIALS OVER Fp
def poly_gcd_ext_mod_prime(a, b, p):
    # Initialize the old and current polynomials for r, s, and t 
    old_r, r = trim(a), trim(b)
    old_s, s = [1], [0]
    old_t, t = [0], [1]
    
    # Iterate until the remainder polynomial becomes zero
    while r!= []:
        # Get the quotient and remainder of the division of old_r by r
        # NOTE: r becomes old_r, and rem becomes r in the next iteration
        quot, rem = poly_div_mod_prime(old_r, r, p)
        old_r, r = r, rem
        
        # Update the s and t polynomials using the quotient
        # NOTE: s becomes old_s, and t becomes old_t in the next iteration
        s_new = poly_sub(old_s, poly_mul(quot, s, p), p)
        old_s, s = s, s_new
        
        # Update the t polynomial similarly
        # NOTE: t becomes old_t, and the t_new becomes the t in the next iteration
        t_new = poly_sub(old_t, poly_mul(quot, t, p), p)
        old_t, t = t, t_new
    
    # Get the leading coefficient of the last non-zero remainder polynomial
    if old_r and old_r!= []:
        lc = old_r[-1]
        lc_inv = pow(lc, p - 2, p)
        old_r = [(c * lc_inv) % p for c in old_r]
        old_s = [(c * lc_inv) % p for c in old_s]
        old_t = [(c * lc_inv) % p for c in old_t]
    
    # Return the last non-zero remainder (the GCD) and the corresponding s and t polynomials
    return old_r, old_s, old_t


# POLYNOMIAL INVERSION FUNCTION
def poly_inverse_mod_prime(f, N, p):
    # Define the polynomial x^N - 1 as a list of coefficients
    xN_1 = [-1] + [0] * (N - 1) + [1]
    
    # Find the GCD of f and x^N - 1
    gcd, s, t = poly_gcd_ext_mod_prime(f, xN_1, p)
    
    # Check if the GCD is 1, which indicates that f is invertible modulo x^N - 1
    if gcd != [1]:
        raise ValueError(f"Polynomial is not invertible modulo prime {p}.")
    
    # Return the inverse polynomial s, trimmed to degree N-1
    return s[:N]


# POLYNOMIAL MULTIPLICATION MODULO (x^N - 1) FUNCTION
def poly_mul_mod_ring(f, g, N, mod=None):
    # Initialize the result list with zeros
    # NOTE: Length equal to N since we are working modulo (x^N - 1)
    res = [0] * N
    
    # Iterate over the coefficients of the first polynomial
    for i in range(len(f)):
        # Iterate over the coefficients of the second polynomial
        for j in range(len(g)):
            # Calculate the index for the result polynomial using modulo N to wrap around
            idx = (i + j) % N
            
            # Update the coefficient of the result polynomial at the calculated index
            res[idx] += f[i] * g[j]
    
    # If a modulus is provided, reduce the coefficients of the result polynomial modulo the given modulus
    if mod is not None:
        res = [c % mod for c in res]
    
    # Return the result polynomial, trimmed to degree N-1
    return res


# FUNCTION TO CENTER COEFFICIENTS IN THE INTERVAL [-mod/2, mod/2 - 1]
def center_mod(f, mod):
    # Initialize the result list to store the centered coefficients
    res = []
    
    # Iterate over the coefficients of the input polynomial
    for c in f:
        # Calculate the centered value by taking the coefficient modulo the given modulus
        val = c % mod
        
        # If the centered value is greater than or equal to half of the modulus, adjust it to be in the negative range
        if val > mod // 2:
            # Adjust the value to be in the range [-mod/2, mod/2 - 1]
            val -= mod
        
        # Append the centered value to the result list
        res.append(val)
    
    # Return the list of centered coefficients
    return res


# INTEGER MODULAR INVERSE FUNCTION
def mod_inverse_int(a, mod):
    # Compute the multiplicative inverse of an integer modulo mod
    a %= mod

    # Check if gcd = 1 to see if there is a modular inverse
    # NOTE: if gcd(a, mod) != 1, then there doesn't exist a x a^-1 = 1 modulo mod
    if math.gcd(a, mod) != 1:
        raise ValueError(f"No modular inverse exists for {a} modulo {mod}.")

    # Initialize the old and current remainders and coefficients
    old_r, r = mod, a
    old_s, s = 0, 1

    # Iterate until r = 0
    while r != 0:
        # Calculate the quotient
        quotient = old_r // r

        # Update the remainders
        old_r, r = r, old_r - quotient * r

        # Update the coefficients
        old_s, s = s, old_s - quotient * s

    # Return the modular inverse
    # NOTE: This is the modular inverse of a modulo mod
    return old_s % mod


# LINEAR SYSTEM MODULO USING GAUSS-JORDAN ELIMINATION FUNCTION
def solve_linear_system_mod(matrix, rhs, mod):
    # Initialize the augmented matrix with the given matrix and right-hand side vector
    size = len(matrix)
    augmented = [row[:] + [rhs[index] % mod] for index, row in enumerate(matrix)]
    row = 0

    # Iterate over the columns of the augmented matrix
    for col in range(size):
        # Initialize the pivot
        pivot = None

        # Check if there is an invertible pivot in the current column
        for candidate in range(row, size):
            if math.gcd(augmented[candidate][col] % mod, mod) == 1:
                pivot = candidate
                break

        # If there is no invertible pivot the column is skipped
        if pivot is None:
            continue

        # Swap the pivot row with the current row
        augmented[row], augmented[pivot] = augmented[pivot], augmented[row]

        # Normalize the pivot row
        pivot_inv = mod_inverse_int(augmented[row][col], mod)
        augmented[row] = [(value * pivot_inv) % mod for value in augmented[row]]

        # Row Elimination
        for other in range(size):
            # Skip the pivot row
            if other == row:
                continue

            # Elimination using row operation
            factor = augmented[other][col] % mod

            # Subtract the scaled pivot row from the current row
            if factor != 0:
                augmented[other] = [
                    (augmented[other][index] - factor * augmented[row][index]) % mod
                    for index in range(size + 1)
                ]

        # Continue to next row if there is
        row += 1
        if row == size:
            break

    # If the number of rows is not equal to the size, then the polynomial is not invertible
    if row != size:
        raise ValueError(f"Polynomial is not invertible modulo {mod}.")

    # Return the inverse polynomial
    return [augmented[index][size] % mod for index in range(size)]


# POLYNOMIAL INVERSION MODULO (x^N - 1) OVER Z_mod FOR ANY POSITIVE MODULUS FUNCTION
def poly_inverse_mod_any_modulus(f, N, mod):
    # Check if the modulus is valid
    if mod <= 1:
        raise ValueError("Modulus must be greater than 1.")

    # Trim the polynomial and reduce coefficients modulo mod
    f_list = [c % mod for c in trim(f)]

    # Check if the polynomial is empty
    if not f_list:
        raise ValueError("Polynomial is not invertible modulo the chosen modulus.")

    # Create the matrix for linear system
    matrix = [[f_list[(row - col) % N] for col in range(N)] for row in range(N)]

    # Set the right-hand side vector
    rhs = [1] + [0] * (N - 1)

    # Solve the linear system
    inverse = solve_linear_system_mod(matrix, rhs, mod)

    # Return the inverse polynomial
    return trim(inverse)

# KEY GENERATION FUNCTION
def ntru_key_generation(N, p, q, f_coeffs, g_coeffs):
    # Generate the private key (fp, fq) and public key h
    # NOTE: the private key is f (fp = f mod p, fq = f mod q)
    f_p = poly_inverse_mod_prime(f_coeffs, N, p)
    f_q = poly_inverse_mod_any_modulus(f_coeffs, N, q)
    h = poly_mul_mod_ring(f_q, g_coeffs, N, q)
    return h, f_coeffs, f_p


# ENCRYPTION FUNCTION
def ntru_encrypt(N, p, q, h, m_coeffs, r_coeffs):
    # Scale random seed by p to make sure it gets reduced to 0 in decryption
    pr = [p * c for c in r_coeffs]

    # Multiply the public key by the random seed
    pr_h = poly_mul_mod_ring(pr, h, N, q)

    # Add the plaintext polynomial to the result
    e = [(pr_h[i] + (m_coeffs[i] if i < len(m_coeffs) else 0)) % q for i in range(N)]

    # Return the ciphertext
    return e


# DECRYPTION FUNCTION
def ntru_decrypt(N, p, q, e, f, f_p):
    # Multiply ciphertext by the private key f
    a = poly_mul_mod_ring(f, e, N, q)
    
    # Center the coefficients modulo q
    a = center_mod(a, q)

    # Multiply the result by the inverse of f mod p
    m = poly_mul_mod_ring(f_p, a, N, p)

    # Center the coefficients modulo p
    m = center_mod(m, p)
    while m and m[-1] == 0:
        m.pop()
    return m


# MAIN FUNCTION
if __name__ == "__main__":
    # Header printing format
    print("=" * 80)
    print("-" * 80)
    title = "NTRU POLY-RING CRYPTOSYSTEM SIMULATION (PURE PYTHON)"
    print(f"| {title.center(76)} |")
    print("-" * 80)

    # Small-scale parameters matching standard verification set
    N_param = 11
    p_param = 3
    q_param = 32

    # Setup polynomials
    f_input = [-1, 1, 1, 0, -1, 0, 1, 0, 0, 1, -1]
    g_input = [-1, 0, 1, 1, 0, 1, 0, 0, -1, 0, -1]
    msg = [-1, 0, 0, 1, -1, 0, 1, 0, 0, -1]
    random_seed = [-1, 0, 1, 1, 0, -1, 0, 0, 1]

    print()
    title = "INITIALIZED VARIABLES"
    print(f"{title.center(80)}")
    print("-" * 80)
    print(f"Parameters chosen: N = {N_param}, p = {p_param}, q = {q_param}")
    print(f"Secret polynomial f(x): {f_input}")
    print(f"Secret polynomial g(x): {g_input}")
    print(f"Original plaintext message m(x): {msg}")
    print(f"Random polynomial r(x): {random_seed}\n")
    print()

    try:
        # Key Generation
        pub_key, priv_f, priv_fp = ntru_key_generation(N_param, p_param, q_param, f_input, g_input)
        title = "KEY GENERATION"
        print(f"{title.center(80)}")
        print("-" * 80)
        print(f"Derived Public Key h(x): {pub_key}\n")
        print()

        # Encryption
        ciphertext = ntru_encrypt(N_param, p_param, q_param, pub_key, msg, random_seed)
        title = "ENCRYPTION"
        print(f"{title.center(80)}")
        print("-" * 80)
        print(f"Generated Ciphertext e(x): {ciphertext}\n")
        print()

        # Decryption
        decrypted_msg = ntru_decrypt(N_param, p_param, q_param, ciphertext, priv_f, priv_fp)
        title = "DECRYPTION"
        print(f"{title.center(80)}")
        print("-" * 80)
        print(f"Decrypted Message m'(x): {decrypted_msg}\n")
        print()

        if decrypted_msg == msg:
            title = "SUCCESS"
            print(f"{title.center(80)}")
            print("-" * 80)
            print("Decrypted message matches the original plaintext!")
            print()
        else:
            title = "FAILED"
            print(f"{title.center(80)}")
            print("-" * 80)
            print("Decryption mismatch detected.")
            print()

    except Exception as err:
        print(f" Simulation failed: {err}")
    print("=" * 80)