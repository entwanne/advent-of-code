import sys

N = 4
signal = sys.stdin.read().strip()

for i in range(len(signal) - N + 1):
    packet = signal[i:i+N]
    if len(set(packet)) == N:
        print(i+N)
        break
