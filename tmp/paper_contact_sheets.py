from pathlib import Path
from PIL import Image, ImageOps, ImageDraw

directory = Path(__file__).resolve().parent / 'paper-render'
pages = sorted(directory.glob('page-*.png'))
for start in range(0, len(pages), 9):
    batch = pages[start:start+9]
    sheet = Image.new('RGB',(1290,1740),'#d9d9d9')
    draw = ImageDraw.Draw(sheet)
    for offset,path in enumerate(batch):
        im = Image.open(path).convert('RGB')
        im = ImageOps.contain(im,(414,540))
        x,y = (offset%3)*430+8,(offset//3)*580+28
        sheet.paste(im,(x,y))
        draw.text((x,y-20),f'Page {start+offset+1}',fill='black')
    output = directory / f'contact-{start//9+1:02}.png'
    sheet.save(output)
    print(output)
