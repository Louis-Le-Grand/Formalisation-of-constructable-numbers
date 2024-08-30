#import tuple from typing
from typing import Tuple
import matplotlib.pyplot as plt

def plot_complex_numbers(numbers, color='blue'):
    for number in numbers:
        plt.plot([0, number.real], [0, number.imag], 'ro-',linestyle='dotted', color=color)
    

def plot_complex_abs(numbers, color='blue'):
    for number in numbers:
        #draw line from (0, complex abs of number) to (number.real, number.imag)
        plt.plot([abs(number), number.real], [0, number.imag], 'ro-', color=color)

def test(n: int):
    z = []
    x = []
    for r in range(2, n+2):
        z.append( 1 + 1j * (r - 1) ** (1 / 2) - r / 2)
        x.append(r / 2)
    return z, x

if __name__ == "__main__":
    z, x = test(100)
    plot_complex_numbers(z)
    plot_complex_numbers(x, 'green')
    plot_complex_abs(z, 'red')
    plt.show()
