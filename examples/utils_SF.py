import re
import json

def extract_title(input_string):
    # Split the input string into lines
    lines = input_string.split('\n')
    
    # Check if there are any lines
    if not lines:
        return None
    
    # Get the first line
    first_line = lines[0]
    
    # Use regex to find the part within parentheses after the word "Exercise"
    pattern = re.compile(r'Exercise.*?\(([^)]*)\)')
    match = pattern.search(first_line)
    
    # Return the matched content if found, otherwise return None
    if match:
        return match.group(1)
    else:
        return None

def extract_content_between_tags(input_string, start_tag, end_tag):
    # Escape the tags to handle any special regex characters
    escaped_start_tag = re.escape(start_tag)
    escaped_end_tag = re.escape(end_tag)
    
    # Use regex to find all content between the specified start and end tags
    pattern = re.compile(rf'{escaped_start_tag}(.*?)\s*{escaped_end_tag}', re.DOTALL)
    matches = pattern.findall(input_string)
    
    return matches

def split_string_by_tag(input_string, tag):
    # Escape the tag to handle any special regex characters
    escaped_tag = re.escape(tag)
    
    # Use the escaped tag with a lookbehind assertion to split the string
    parts = re.split(f'({escaped_tag})', input_string)
    
    # Combine each tag with the preceding part
    combined_parts = [parts[i] + parts[i+1] for i in range(0, len(parts) - 1, 2)]

    # If there's a trailing part without a tag, add it to the result
    if len(parts) % 2 != 0:
        combined_parts.append(parts[-1])
    
    return combined_parts

Definition_tag = "_your_definition_"
Proof_tag = "(* FILL IN HERE *)"

def extract_parts_to_json(input_file, output_file=None, start_tag='(** **** Exercise:', end_tag='[] *)'):
    # Read the contents of the input file
    with open(input_file, 'r') as file:
        data = file.read()
    
    # Use regex to find all parts between the specified start and end tags
    pattern = re.compile(rf'{re.escape(start_tag)}.*?{re.escape(end_tag)}', re.DOTALL)
    matches = pattern.findall(data)
    

    extracted_parts = [{f'exercise_{i}': match.strip()} for (i,match) in enumerate(matches)]
    for (i,extract) in enumerate(extracted_parts):
        extract['title'] = extract_title(extract[f'exercise_{i}'])
        split_parts = split_string_by_tag(extract[f'exercise_{i}'], tag='Admitted.\n')
        extract['parts'] = split_parts
        extract['type_parts'] = []
        extract['names'] = []
        for i, part in enumerate(split_parts):
            last_line = part.strip().split('\n')[-1]
            if Definition_tag in last_line:
                extract['type_parts'].append('Definition')
                extract['names'].append('tbd')
            elif Proof_tag in last_line:
                extract['type_parts'].append('Proof')
                name = extract_content_between_tags(part, start_tag='Theorem ', end_tag=':')
                extract['names'].append(name)
            else:
                extract['type_parts'].append('End')
                extract['names'].append('end')
    
    # Write the extracted parts to a JSON file
    if output_file is not None:
        with open(output_file, 'w') as json_file:
            json.dump(extracted_parts, json_file, indent=4)
    
    return extracted_parts