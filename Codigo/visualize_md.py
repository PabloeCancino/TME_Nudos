import markdown
import sys
import os
import webbrowser

def render_markdown(filename):
    if not os.path.exists(filename):
        print(f"Error: File {filename} not found.")
        return

    with open(filename, 'r', encoding='utf-8') as f:
        text = f.read()

    # Basic conversion
    html_body = markdown.markdown(text, extensions=['tables', 'fenced_code'])

    # HTML Template with MathJax
    html_content = f"""
<!DOCTYPE html>
<html>
<head>
    <meta charset="utf-8">
    <title>{os.path.basename(filename)}</title>
    <style>
        body {{
            font-family: -apple-system, BlinkMacSystemFont, "Segoe UI", Helvetica, Arial, sans-serif;
            line-height: 1.6;
            max-width: 800px;
            margin: 0 auto;
            padding: 20px;
            color: #333;
            background-color: #f9f9f9;
        }}
        h1, h2, h3 {{ color: #2c3e50; border-bottom: 1px solid #eaecef; padding-bottom: 0.3em; }}
        code {{ background-color: #f0f0f0; padding: 0.2em 0.4em; border-radius: 3px; font-family: monospace; }}
        pre {{ background-color: #f6f8fa; padding: 16px; overflow: auto; border-radius: 6px; }}
        blockquote {{ border-left: 4px solid #dfe2e5; color: #6a737d; padding-left: 1em; margin-left: 0; }}
        table {{ border-collapse: collapse; width: 100%; margin: 15px 0; }}
        th, td {{ border: 1px solid #dfe2e5; padding: 6px 13px; }}
        th {{ background-color: #f6f8fa; }}
        .math-display {{ overflow-x: auto; }}
    </style>
    
    <!-- MathJax Configuration -->
    <script>
    window.MathJax = {{
      tex: {{
        inlineMath: [['$', '$'], ['\\\\(', '\\\\)']],
        displayMath: [['$$', '$$'], ['\\\\[', '\\\\]']],
        processEscapes: true
      }},
      options: {{
        skipHtmlTags: ['script', 'noscript', 'style', 'textarea', 'pre']
      }}
    }};
    </script>
    <script id="MathJax-script" async src="https://cdn.jsdelivr.net/npm/mathjax@3/es5/tex-mml-chtml.js"></script>
</head>
<body>
    {html_body}
</body>
</html>
    """

    output_filename = filename + ".html"
    with open(output_filename, 'w', encoding='utf-8') as f:
        f.write(html_content)
    
    print(f"Rendered to {output_filename}")
    webbrowser.open('file://' + os.path.abspath(output_filename))

if __name__ == "__main__":
    if len(sys.argv) > 1:
        filename = sys.argv[1]
    else:
        # Default file if none specified
        filename = "Presentacion/TEORIA_FUNDAMENTAL_NUDOS_RACIONALES.md"
    
    render_markdown(filename)
