import re
from collections import Counter
def find_words_starting_with_st(file_path):
    with open(file_path, 'r') as file:
        text = file.read()
    print(text)
    # 使用正则表达式找到所有以 st_ 开头的单词
    pattern = r'\bwt_\w*\b'
    words = re.findall(pattern, text)

    return words
def count_elements(arr):
    counts = {}
    for elem in arr:
        if elem in counts:
            counts[elem] += 1
        else:
            counts[elem] = 1
    return counts
# 示例使用
file_path = '/home/logic/project/velus/ST/Correctness.v'  # 替换为你的文件路径
words = find_words_starting_with_st(file_path)
count = count_elements(words)
print(count)