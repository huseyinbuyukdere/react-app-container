/// <reference types="react" />
interface IconComponentProps {
    name: string;
    height?: string;
    width?: string;
    fill?: string;
    className?: string;
    style?: any;
}
declare const IconComponent: (props: IconComponentProps) => JSX.Element | null;
export default IconComponent;
